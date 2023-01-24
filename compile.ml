(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32

let alloc_string =
  (* ajoute string dans table + renvoit code assembleur de nouveau str *)
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  (* renvoit code assembleur de nouveau label *)
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  mutable nb_locals: int; (* maximum du nb de variables *)
  mutable size: int;
  next_local: int; (* 0, 1, ... *)
  table_adr: (int, int) Hashtbl.t; (* stocks var adresses *)
  table_res: (int, int) Hashtbl.t (* stocks res adresses *)
}

(*let empty_env =
  let locals_empty : (string, structure) Hashtbl.t = Hashtbl.create 10
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0}*)

let mk_bool d = { expr_desc = d; expr_typ = Tbool }



(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end


let rec expr env e = match e.expr_desc with

  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
    movq (ilab (alloc_string s)) (reg rdi)

  | TEbinop (Band, e1, e2) ->
    (* if e1 then e2 else false *)

    expr env begin
      mk_bool ( TEif(e1, e2, (mk_bool (TEconstant (Cbool false)) ) ) )
    end

  | TEbinop (Bor, e1, e2) ->
    (* if e1 then true else e2 *)

    expr env begin
      mk_bool ( TEif(e1, (mk_bool (TEconstant (Cbool true))), e2 ) )
    end

  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    (* eval e1 then e2 then cmpr *)

    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rsi ++ (* cmpq ?? *)
    compile_bool begin
      match op with
      | Blt -> jge 
      | Ble -> jg 
      | Bgt -> jle
      | Bge -> jl
      | _ -> failwith "weird"
    end

  | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) ->
    (* eval e1 then e2 then operation *)

    expr env e1 ++
    pushq (reg rdi) ++ (* reg rdi = !%rdi *)
    expr env e2 ++
    popq rsi ++
    begin
      match op with
      | Badd -> addq (reg rsi) (reg rdi)
      | Bsub -> subq (reg rsi) (reg rdi)
      | Bmul -> imulq (reg rsi) (reg rdi)
      | Bdiv -> movq (reg rsi) (reg rax) ++ cqto ++  idivq (reg rdi) ++ movq (reg rax) (reg rdi)
      | Bmod -> movq (reg rsi) (reg rax) ++ cqto ++  idivq (reg rdi) ++ movq (reg rdx) (reg rdi)
      | _ -> failwith "weird"
    end
    
  | TEbinop (Beq | Bne as op, e1, e2) ->
    (* Tptr ? si struct utilise memcmp de stdlib : callq memcmp -> résultat = negq rax
        - dest : rdi
        - src : rsi
        - size : rdx vérif *)

    let conclusion = compile_bool begin
      match op with
      | Beq -> je
      | Bne -> jne
      | _ -> failwith "weird"
    end
    in
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rsi ++
    begin match e1.expr_typ with
    | Tint |Tptr(_) ->
      cmpq (reg rsi) (reg rdi) ++
      conclusion 
    | Tbool ->
      movq (reg rdi) (reg rdx) ++
      negq (reg rdx) ++
      andq (reg rsi) (reg rdi) ++
      negq (reg rsi) ++
      andq (reg rdx) (reg rsi) ++
      orq (reg rsi) (reg rdi)
    | Tstring ->
      (*str*)cmpq (reg rsi) (reg rdi) ++
      conclusion
    | Tptrnil | Twild -> movq (imm 0) (reg rdi)
    | _ -> failwith "weird"
    end

  | TEunop (Uneg, e1) ->
    (* négation int *)

    expr env e1 ++
    negq (reg rdi)

  | TEunop (Unot, e1) ->
    (* négation booléen *)

    expr env e1 ++
    notq (reg rdi)

  | TEunop (Uamp, e) ->
    (* & required l-value
       we just want adresses *)

    begin match e.expr_desc with
    | TEident(v) ->
      (*if v.v_name = "_" then movq (imm64 0) (reg rdi) else*)
      (* a = adress of v in stack *)
      if !debug then print_string ("Uamp : finding location of " ^ (string_of_int v.v_id) ^" in stack \n");
      let a = Hashtbl.find env.table_adr v.v_id in
      if !debug then print_string ("found \n");
      movq (imm a) (reg rdi)
    | TEdot(e1, x) ->
      expr env {expr_desc = TEunop(Uamp, e1); expr_typ = Tptr e1.expr_typ } ++
      addq (imm x.f_ofs) (reg rdi)
    | TEunop(Ustar, e1) ->
      expr env e1
    | _ -> failwith "not l-value, weird"
    end

  | TEunop (Ustar, e) ->
    (* star
       we want the value, look into the pile *)

    expr env e ++
    movq (ind rbp) (reg rdi)

  | TEprint el ->
    
    let print_ code e =
      code ++
      expr env e ++
      begin match e.expr_typ with
      | Tint | Tptr(_) -> call "print_int"
      | Tbool -> call "print_bool"
      | Tstring -> call "print_string"
      | Twild | Tptrnil -> call "print_nil"
      | Tstruct(stru) ->
        let rec aux fieldli =
        movq (ilab (alloc_string stru.s_name)) (reg rdi) ++
        call "print_string" ++
        begin match fieldli with
        | [] -> nop
        | fie :: reste_fields ->
          movq (ilab "S_nextline") (reg rdi) ++
          call "print_string" ++
          movq (ind ~ofs:(fie.f_ofs) ~index:rdi rbp) (reg rdi) ++
          (match fie.f_typ with
          |  Tint | Tptr(_) -> call "print_int"
          | Tbool -> call "print_bool"
          | Tstring -> call "print_string"
          | Twild | Tptrnil -> call "print_nil"
          | _ -> failwith "im worried about how to print some types within structures")
          (* missing Tmany within structures ? *)
        end in
        movq (ilab (alloc_string stru.s_name)) (reg rdi) ++
        call "print_string" ++
        aux stru.s_ordered_fields
      | _ -> failwith "im worried about how to print some types"
      end
      ++ movq (ilab "S_nextline") (reg rdi)
      ++ call "print_string"
    in List.fold_left print_ nop el

  | TEident x ->

    if !debug then print_string ("ident : finding location of " ^ (string_of_int x.v_id) ^" in stack \n");
    let a = Hashtbl.find env.table_adr x.v_id in
    if !debug then print_string ("found \n");
    movq (ind ~ofs:a rbp) (reg rdi)

  | TEassign (lv, el) ->
    (* code pour x1,... := e1,... *)

      let assign_one v e = (* v var, e expr, code pour v := e *)
        if !debug then print_string ("assign : finding location of " ^ (string_of_int v.v_id) ^" in stack \n");
        expr env e ++ begin
        (* if x.v_name = "_" then nop else *)
        let a = Hashtbl.find env.table_adr v.v_id in (* a adress of v in stack *)
        if !debug then print_string ("found \n");
        movq (reg rdi) (ind ~ofs:a rbp) end
      in
      let assign code v =
        code ++
        expr env {expr_desc = TEunop(Uamp, {expr_desc = v.expr_desc; expr_typ = v.expr_typ}); expr_typ = Tptr v.expr_typ} ++ (* fetch adress of value *)
        popq rsi ++
        movq (reg rsi) (ind ~index:rdi rbp) 
      in
      begin match (lv, el) with
        | ([], []) -> nop
        | ([{expr_desc = TEident v}], [e]) ->
          assign_one v e
        | ( _ :: _, [{expr_desc = TEcall(_,_)} as e]) -> (*e.expr_desc = expr_desc = TEcall(f, elf)*)
          expr env e ++ (* return puts the expressions already on the stack *)
          List.fold_left assign nop lv (* destack and give values to adresses of lv *)
        | (lv, el) -> 
          List.fold_left (fun code e -> expr env e ++ pushq (reg rdi) ++ code) nop el ++ (* mettre exprs sur la pile *)
          List.fold_left assign nop lv (* destack and give values to adresses of lv *)
      end

  | TEblock el ->

    let aux code v =
      if v.v_name = "_" then nop else
      begin Hashtbl.add env.table_adr v.v_id (-env.size);
      if !debug then print_string ("added var id " ^ (string_of_int v.v_id) ^ " in table_adr : address in stack " ^(string_of_int (-env.size)) ^"\n");
      env.nb_locals <- env.nb_locals + 1;
      env.size <- env.size + sizeof v.v_typ;
      code ++
      addq (imm (-(sizeof v.v_typ))) !%rsp (* might not work ... *)
      end
    in

    let rec code = ( function
      | [] -> nop
      | {expr_desc = TEvars(varli, exprli)} :: reste_expr ->
        let t :: _ = varli in
        let vli = List.map (fun v -> {expr_desc = TEident(v); expr_typ = v.v_typ}) varli in
        let codeli = List.fold_left aux nop varli in
        let code1 = expr env {expr_desc = TEassign(vli, exprli); expr_typ = t.v_typ} in
        codeli ++
        code1 ++
        code reste_expr
      | e :: reste_expr ->
        let code1 = expr env e in
        code1 ++ code reste_expr )
    in code  el

  | TEif (e1, e2, e3) ->
    (* eval e1 puis conditionner *)

    let l_false = new_label() in
    let l_end = new_label() in

    expr env e1 ++
    cmpq (imm 0) (reg rdi) ++
    je l_false ++
    expr env e2 ++
    jmp l_end ++
    label l_false ++
    expr env e3 ++
    label l_end

  | TEfor (e1, e2) ->
    (* eval e1 *)

    let l_test = new_label() in
    let l_loop = new_label() in

    jmp l_test ++
    label l_loop ++ (* main loop *)
    expr env e2 ++
    (* jmps to l_test *)
    label l_test ++ (* test loop *)
    expr env e1 ++
    testq (reg rdi) (reg rdi) ++ (* might not work... *)
    je l_loop

  | TEnew ty ->
     (* code pour new S *)

     malloc (sizeof ty) (* ???? I COPIED this *)

  | TEcall (f, el) ->
    (* add space for res at the top of stack
       add arguments of f
       call f *)

    let rec add_params exprlist paramli = ( match (exprlist, paramli) with
    | ([], []) -> nop
    | ([{expr_desc = TEcall(_,_)} as p], lv) ->
      expr env p (* return pushes list onto the stack *)
    | (e1 :: q1, v :: q) -> let code = add_params q1 q in
      code ++
      expr env e1 ++ 
      pushq (reg rdi)
    | _ -> failwith "weird" )
    in
    let vli = List.map (fun v -> {expr_desc = TEident(v); expr_typ = v.v_typ}) f.fn_params in
    let size_res = List.fold_left (fun n ty -> n + (sizeof ty)) 0 f.fn_typ in (* space to give to res *)
    subq (imm size_res) (reg rsp)  ++ (* add res *)
    add_params el vli ++  (* add params *)
    call ("F_" ^ f.fn_name)

  | TEdot (e1, {f_ofs=ofs}) ->
    (* chercher l'adresse de e1, rajouter l'offset *)

    expr env {expr_desc = TEunop(Uamp, e1); expr_typ = Tptr e1.expr_typ} ++
    movq (ind ~ofs:(-ofs) rbp) (reg rdi)

  | TEvars _ ->

    nop

  | TEreturn [] ->

    call env.exit_label

  (* | TEreturn [e1] ->
    (* code pour return e1 *)

    expr env e1 ++
    movq (reg rdi) (reg rax) ++
    call env.exit_label *)

  | TEreturn el ->
    (* basically like TEassign but I don't have a Hashtbl with the vars *)

    let rec assign n = begin function
      | [] -> nop
      | _ :: reste_expr ->
        if !debug then print_string ("looking for address of res number " ^ (string_of_int n) ^ " in table_res \n");
        let a = Hashtbl.find env.table_res n in
        begin if !debug then print_string ("found \n");
        popq rdi ++
        movq (reg rdi) (ind ~ofs:a rbp) ++
        assign (n+1) reste_expr end
    end in 
    List.fold_left (fun code e -> expr env e ++ pushq (reg rdi) ++ code) nop el ++
    assign 0 el ++
    call env.exit_label

  | TEincdec (e, Inc) ->
    (* e++ *)

    expr env {expr_desc = TEunop(Uamp, e); expr_typ = Tptr e.expr_typ} ++
    addq (imm 1) (ind ~index:rdi rbp) ++
    movq (ind ~index:rdi rbp) (reg rdi)
  
  | TEincdec(e, Dec) ->
    (* e-- *)

    expr env {expr_desc = TEunop(Uamp, e); expr_typ = Tptr e.expr_typ} ++
    decq (ind ~index:rdi rbp) ++
    movq (ind ~index:rdi rbp) (reg rdi)





let function_ f e =
  if !debug then print_string ("function " ^ f.fn_name ^ " : \n");
  (* code pour les fonctions *)
  
  let s = f.fn_name in
  let length = List.length f.fn_params in
  let table_res : (int, int) Hashtbl.t = Hashtbl.create 10 in
  (* rajouter les paramètres à la table *)
  let table : (int, int) Hashtbl.t = Hashtbl.create 10 in
  let rec add_params vli adr_ = match vli with
    | [] -> adr_
    | v :: reste -> Hashtbl.add table v.v_id (adr_);
    if !debug then print_string ("added var id " ^ (string_of_int v.v_id) ^ " to table_adr : address in stack " ^(string_of_int (adr_ + (sizeof v.v_typ))) ^"\n") ;
    add_params reste (adr_ + (sizeof v.v_typ))
  in
  let adr_ = add_params f.fn_params 0 in
  (* ajouter des variables res1, ... resk pour le return *)
  let rec add_res n adr_ = function
    | [] -> ()
    | ty :: reste_ty ->
      Hashtbl.add table_res n (adr_) ;
      if !debug then print_string ("added res number " ^ (string_of_int n) ^ " to table_res : address in stack " ^(string_of_int (adr_ + sizeof(ty))) ^"\n");
      add_res (n+1) (adr_ + sizeof(ty)) reste_ty
  in add_res 0 adr_ f.fn_typ;
  (* créer l'environnement *)
  let env =
    {exit_label = "E_" ^ s ;
    ofs_this = length-1;
    nb_locals = 0;
    size = 0;
    next_local = 0;
    table_adr = table;
    table_res = table_res} in

  if !debug then print_string ("starting code : \n");

  label ("F_" ^ s)
  ++ pushq (reg rbp)
  ++ movq (reg rsp) (reg rbp)
  ++ expr env e
  ++ label ("E_" ^ s)
  ++ movq(reg rbp) (reg rsp)
  ++ popq rbp
  (* ++ movq (ind ~ofs:adr_ rsp) (reg rbp) *)
  ++ ret



let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code



let file ?debug:(b=false) dl =
  debug := b;

  (* calcul offset des champs *)
  let offset name field_ n =

    if b then print_string ("\tfield '" ^ field_.f_name ^ "' has offset "
          ^ string_of_int n ^ "\n") ;
    field_.f_ofs <- n;
    n + (sizeof field_.f_typ) 
  in
  let rec aux_ofs = function
    | [] -> ()
    | TDstruct(stru) :: q ->
      if b then print_string("Working on structure " ^ stru.s_name ^ "\n");
      let _ = Hashtbl.fold offset stru.s_fields 0 in
      aux_ofs q
    | _ :: q -> aux_ofs q
  in aux_ofs dl;

  if b then print_string "working on functions \n";

  let funs = List.fold_left decl nop dl in

  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "




print_int_or_nil:
      test    %rdi, %rdi
      jz      print_nil
      movq    (%rdi), %rdi
print_int:
      movq    %rdi, %rsi
      movq    $S_int, %rdi
      xorq    %rax, %rax
      call    printf
      ret
print_string:
      test    %rdi, %rdi
      jz      print_nil
      mov     %rdi, %rsi
      mov     $S_string, %rdi
      xorq    %rax, %rax
      call    printf
      ret
print_nil:
      mov     $S_nil, %rdi
      xorq    %rax, %rax
      call    printf
      ret
print_space:
      mov     $S_space, %rdi
      xorq    %rax, %rax
      call    printf
      ret
print_bool:
      xorq    %rax, %rax
      test    %rdi, %rdi
      jz      1f
      mov     $S_true, %rdi
      call    printf
      ret
1:      mov     $S_false, %rdi
      call    printf
      ret
allocz:
      movq    %rdi, %rbx     # callee-save
        call    malloc
        testq   %rbx, %rbx
        jnz     1f
        ret
1:      movb    $0, (%rax, %rbx)
        decq    %rbx
        jnz     1b
        ret
"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
      label "S_string" ++ string "%s" ++
      label "S_true" ++ string "true" ++
      label "S_false" ++ string "false" ++
      label "S_nil" ++ string "<nil>" ++
      label "S_space" ++ string " " ++
      label "S_empty" ++ string "" ++
      label "S_nextline" ++ string "\n" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
