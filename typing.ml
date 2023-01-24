
open Format
open Usage
open Lib
open Ast
open Tast

let debug = ref false
let found_main = ref false
let fmt_used = ref false
let fmt_imported = ref true

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos
exception Error of Ast.location * string
exception Anomaly of string


let tvoid = Tmany []

let rec printable_type = function
  | Tint -> "int"
  | Tbool -> "bool"
  | Tstring -> "string"
  | Tstruct structure -> structure.s_name
  | Tptrnil -> "<nil>"
  | Twild -> "<wild>" (* for internal purpose only *)
  | Tptr typ -> "*" ^ (printable_type typ)
  | Tmany [] -> "instruction"
  | Tmany [t] -> printable_type t ^ " (·)"
  | Tmany (t :: q) -> (printable_type t) ^ " · " ^ (printable_type (Tmany q))

let type_error_message expected received =
  "This expression has type '" ^ (printable_type received)
  ^ "' but an expression of type '" ^ (printable_type expected) ^ "' was expected"

let incorrect_wild_use = "cannot use _ as value"

(* context types *)
type struct_env = structure M.t
type fun_env = function_ M.t

(* expression associated with a variable *)
let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let wildvar = {
  v_name = "_"; v_id = -1;
  v_loc = dummy_loc; v_typ = Twild;
  v_depth = 0; v_used = true; v_addr = 0 
}


let new_var =
  let id = ref 0 in
  fun x loc ?(depth=0) ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty;
      v_depth = depth; v_used = used; v_addr = 0 }

module Env = struct
  type e = {
    vars: var M.t;
    functions: fun_env;
    structures: struct_env;
    return_values: typ list;
    returns: bool;
    depth: int;
  }

  let push_down env = {env with depth = env.depth + 1}
  let find_opt id env = M.find_opt id env.vars
  let add env v = {env with vars=(M.add v.v_name v env.vars)}
  let add_vars = List.fold_left add

  let new_env functions structures f = add_vars {
    vars=M.empty;
    functions; structures;
    return_values=f.fn_typ;
    returns=false;
    depth=0
  } f.fn_params

  let all_vars = ref []
  let check_unused () =
    List.iter (fun v -> if v.v_name <> "_" && not v.v_used
      then raise (Error (v.v_loc, "unused variable '" ^ v.v_name ^ "'")))
    !all_vars

  let var x loc ty ?(used=false) env = match x, ty with
      | _, Tmany _ | _, Tptrnil -> raise (Error (loc,
          "variable '" ^ x ^ "' may not have type '" ^ printable_type ty ^ "'"))

      | "_", _ -> env, wildvar

      | _, _ -> let v = new_var x loc ty ~used ~depth:env.depth in
          all_vars := v :: !all_vars;
          begin match find_opt x env with
            | None -> add env v, v
            | Some v' -> if env.depth > v'.v_depth
                then add env v, v
                else raise (Error (loc, "variable '" ^ x ^ "' already defined"))
          end
end


(* associate precise type if valid in a given structure context *)
(* replacement for the original 'type_type' function *)
let rec find_type structures = function
  | PTptr ptyp -> Tptr (find_type structures ptyp)
  | PTident {id = "int"; loc} -> Tint
  | PTident {id = "bool"; loc} -> Tbool
  | PTident {id = "string"; loc} -> Tstring
  | PTident {id; loc} -> if M.mem id structures
      then Tstruct (M.find id structures)
      else raise (Error (loc, "unknown type '" ^ id ^ "'"))

(* Tests equality between types. *)
(* instruction types (Tmany []) shall never be tested *)
let rec eq_type ty1 ty2 =
  match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tptrnil, Tptr _ | Tptr _, Tptrnil -> true
  | Twild, _ | _, Twild -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false

let rec correspondance param loc typ1 typ2 = match typ1, typ2 with
  | [], [] -> ()
  | _, [] -> raise (Error (loc, "not enough " ^ param))
  | [], _ -> raise (Error (loc, "too many " ^ param))
  | (lt :: lq), (et :: eq) -> if eq_type lt et
      then correspondance param loc lq eq
      else raise (Error (loc, type_error_message lt et))

let call_correspondance = correspondance "parameters"
let assignation_correspondance = correspondance "values to unpack"
let return_correspondance = correspondance "returned values"

let rec lvalue_test {expr_desc} = match expr_desc with
  | TEdot (e, x) -> lvalue_test e
  | TEident _ -> true
  | TEunop (Ustar, _) -> true
  | _ -> false


let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = {expr_desc=d; expr_typ=tvoid} (* statement *)


(* types an expression and returns a possibly modified environment *)
let rec expr (env: Env.e) e =
  let e, ty, env' = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, env'

and expr_desc env loc = function
  | PEskip -> TEskip, tvoid, env

  | PEconstant c -> begin match c with
      | Cint _ -> TEconstant c, Tint, env
      | Cstring _ -> TEconstant c, Tstring, env
      | Cbool _ -> TEconstant c, Tbool, env
    end

  | PEbinop (op, e1, e2) ->
      let e1', _ = expr env e1 and e2', _ = expr env e2 in
      let {expr_typ=t1} = e1' and {expr_typ=t2} = e2' in
      begin match op with
        | Badd | Bsub | Bmul | Bdiv | Bmod ->
            begin match t1, t2 with
              | Tint, Tint -> TEbinop (op, e1', e2'), Tint, env
              | Tint, _ -> raise (Error (e2.pexpr_loc, type_error_message Tint t2))
              | _, _ -> raise (Error (e1.pexpr_loc, type_error_message Tint t1))
            end
        | Beq | Bne -> if eq_type t1 t2
            then TEbinop (op, e1', e2'), Tbool, env
            else raise (Error (loc, "expressions do not have the same type"))
        | Blt | Ble | Bgt | Bge ->
            begin match t1, t2 with
              | Tint, Tint -> TEbinop (op, e1', e2'), Tbool, env
              | Tint, _ -> raise (Error (e2.pexpr_loc, type_error_message Tint t2))
              | _, _ -> raise (Error (e1.pexpr_loc, type_error_message Tint t1))
            end
        | Band | Bor ->
            begin match t1, t2 with
              | Tbool, Tbool -> TEbinop (op, e1', e2'), Tbool, env
              | Tbool, _ -> raise (Error (e2.pexpr_loc, type_error_message Tbool t2))
              | _, _ -> raise (Error (e1.pexpr_loc, type_error_message Tbool t1))
            end
      end
    
  | PEunop (Uamp, e1) ->
      let e1', _ = expr env e1 in if lvalue_test e1'
        then TEunop (Uamp, e1'), Tptr e1'.expr_typ, env
        else raise (Error (e1.pexpr_loc, "lvalue required as operand of '&'"))
      
  | PEunop (Uneg | Unot | Ustar as op, e1) ->
      let e1', _ = expr env e1 in begin match op, e1'.expr_typ with
        | Uneg, Tint -> TEunop (Uneg, e1'), Tint, env
        | Uneg, t -> raise (Error (e1.pexpr_loc, type_error_message Tint t))
        | Unot, Tbool -> TEunop (Unot, e1'), Tbool, env
        | Unot, t -> raise (Error (e1.pexpr_loc, type_error_message Tbool t))
        | Ustar, Tptrnil -> raise (Error (e1.pexpr_loc, "cannot dereference nil"))
        | Ustar, Tptr t -> TEunop (Ustar, e1'), t, env
        | _ -> raise (Error (e1.pexpr_loc, "cannot dereference this"))
      end  

  | PEcall ({id = "fmt.Print"; loc}, el) ->
      if not !fmt_imported then raise (Error (loc, "unknown function 'fmt.Print'"));
      let el', typ_list = expr_list env el in
      List.iter (function
        | Tmany _ -> raise (Error (loc, "this is not a correct expression, it cannot be printed"))
        | _ -> ()) typ_list;
      fmt_used := true;
      TEprint el', tvoid, env

  | PEcall ({id="new"}, [{pexpr_desc=PEident ident}]) ->
      let t = find_type env.structures (PTident ident) in TEnew t, Tptr t, env
  | PEcall ({id="new"}, _) -> raise (Error (loc, "new expects a type"))

  | PEcall ({id; loc}, el) -> begin match M.find_opt id env.functions with
      | Some callee -> 
          let el', typ_list = expr_list env el in
          call_correspondance loc typ_list
            (List.map (fun v -> v.v_typ) callee.fn_params);
          let ret_typ = match callee.fn_typ with
            | [t] -> t
            | l -> Tmany l
          in
          TEcall (callee, el'), ret_typ, env
      | None -> raise (Error (loc, "unknown function '" ^ id ^ "'"))     
    end

  | PEfor (b, e) ->
      let e', _ = expr env e and b', _ = expr env b in
      begin match e'.expr_typ, b'.expr_typ with
        | Tmany [], Tbool -> TEfor (b', e'), tvoid, env
        | _, Tbool -> raise (Error (loc, "syntax error"))
        | _, t -> raise (Error (b.pexpr_loc, type_error_message Tbool t))
      end

  | PEif (b, e1, e2) ->
      let e1', env1 = expr env e1
      and e2', env2 = expr env e2
      and b', _ = expr env b in
      begin match b'.expr_typ, e1'.expr_typ, e2'.expr_typ with
        | Tbool, Tmany [], Tmany [] -> TEif (b', e1', e2'), tvoid,
            {env with returns = env.returns || (env1.returns && env2.returns)}
        | Tbool, _, _ -> raise (Error (loc, "syntax error"))
        | _, _, _ -> raise (Error (b.pexpr_loc, type_error_message Tbool b'.expr_typ))
      end

  | PEnil -> TEnil, Tptrnil, env
      
  | PEident {id} -> begin match Env.find_opt id env, id with
      | _, "_" -> raise (Error (loc, incorrect_wild_use))
      | Some v, _ -> v.v_used <- true; TEident v, v.v_typ, env
      | None, _ -> raise (Error (loc, "unknown variable '" ^ id ^ "'"))
    end

  | PEdot (e, {id; loc=id_loc}) ->
      let e', _ = expr env e in begin match e'.expr_typ with
        | Tptr (Tstruct structure) | Tstruct structure ->
            begin match Hashtbl.find_opt structure.s_fields id with
              | Some field -> TEdot (e', field), field.f_typ, env
              | None -> raise (Error (id_loc, "structure '" ^ structure.s_name
                  ^ "' has no field named '" ^ id ^ "'"))
            end
        | _ -> raise (Error (e.pexpr_loc,
            "this is not a valid structure nor a pointer to a structure"))
      end

  | PEassign (lvl, el) ->
      let lvl', lvl_typ = expr_list ~wildcard:true env lvl
      and el', el_typ = expr_list env el in
      List.iter (fun e -> if not (lvalue_test e)
        then raise (Error (loc, "this is not an lvalue, it cannot be assigned a value"))) lvl';
      assignation_correspondance loc lvl_typ el_typ;
      TEassign (lvl', el'), tvoid, env

  | PEreturn el ->
      let el', el_typ = expr_list env el in
      return_correspondance loc env.return_values el_typ;
      TEreturn el', tvoid, {env with returns = true}

  | PEblock el ->
      let has_already_returned = ref false in
      let rec iter_block env = function
        | e :: t -> let e', env' = expr env e in begin match e'.expr_typ with
            | Tmany [] -> let el', env_f = iter_block env' t in
                if env.returns && not !has_already_returned
                  then (warning e.pexpr_loc "instructions after return instruction"; has_already_returned := true);
                e' :: el', env_f
            | _ -> raise (Error (loc, "this is not an instruction"))
          end
        | [] -> [], env
      in
      let el', env_f = iter_block (Env.push_down env) el in
      TEblock el', tvoid, {env with returns = env_f.returns}

  | PEincdec (e, op) ->
      let ops = if op = Inc then "increment" else "decrement" in
      let e', _ = expr env e in begin match e'.expr_typ with
        | Tint -> if lvalue_test e'
            then TEincdec (e', op), tvoid, env
            else raise (Error (loc, "lvalue required as " ^ ops ^ " operand")) 
        | t -> raise (Error (loc, type_error_message Tint t))
      end

  | PEvars (ids, ptypo, el) ->
      let el', typ_list = expr_list env el in
      let env', varlist, assignlist = match ptypo, el' with
        | Some ptyp, [] ->
            let typ = find_type env.structures ptyp in
            let nilexpr = {expr_desc = TEnil; expr_typ = Tptrnil} in
            (* NOTE: This works because structures and structure pointers are treated almost equally. *)
            let newexpr = {expr_desc = TEnew typ; expr_typ = Tptrnil} in
            let rec instanciate env varlist assignlist = function 
              | [] -> env, varlist, assignlist
              | id :: iq ->
                  let env', v = Env.var id.id id.loc typ env in
                  instanciate env' (v :: varlist)
                    ((match typ with Tstruct _ -> newexpr | _ -> nilexpr) :: assignlist) iq
            in
            instanciate env [] [] ids
            
        | None, _ ->
            let rec instanciate env varlist ids l = match ids, l with
              (* accumulated list is reversed in order to match that of initialisation values *)
              | [], [] -> env, List.rev varlist, el'
              | _, [] -> raise (Error (loc, "not enough values to unpack"))
              | [], _ -> raise (Error (loc, "too many values to unpack"))
              | (id :: iq), (t :: q) ->
                  let env', v = Env.var id.id id.loc t env in
                    instanciate env' (v :: varlist) iq q
            in
            instanciate env [] ids typ_list

        | Some ptyp, _ ->
            let typ = find_type env.structures ptyp in
            let rec instanciate env varlist ids l = match ids, l with
              | [], [] -> env, List.rev varlist, el'
              | _, [] -> raise (Error (loc, "not enough values to unpack"))
              | [], _ -> raise (Error (loc, "too many values to unpack"))
              | (id :: iq), (t :: q) -> if eq_type t typ
                  then begin
                    let env', v = Env.var id.id id.loc typ env in
                    instanciate env' (v :: varlist) iq q
                  end
                  else raise (Error (loc, type_error_message typ t))
            in
            instanciate env [] ids typ_list
      in
      TEvars (varlist, assignlist), tvoid, env'

(* evaluates a list of expression (including function calls with multiple return values) *)
(* the wildcard flag allows the use of _ (in the left part of an assignation for instance) *)
and expr_list ?(wildcard=false) env = function
  | [({pexpr_desc=PEcall _} as call)] ->
      let e, _ = expr env call in
      begin match e.expr_typ with
        | Tmany l -> [e], l
        | t -> [e], [t]
      end
  | l -> let l' = List.map (function
      | {pexpr_desc = PEident {id = "_"}} when wildcard -> evar wildvar, Twild
      | {pexpr_desc = PEident {id = "_"; loc}} -> raise (Error (loc, incorrect_wild_use))
      | e -> let e', _ = expr env e in e', e'.expr_typ) l in
      List.split l'

(* 1. declare structures *)
(* builds a *typed* structure environment, with at first no field *)
let phase1 structures = function
  | PDstruct {ps_name = {id = ("int" | "bool" | "string") as id; loc}; _} ->
      raise (Error (loc, "redefinition of type primitive '" ^ id ^ "'"))
  | PDstruct {ps_name = {id; loc}; _} ->
      if M.mem id structures
        then raise (Error (loc, "structure '" ^ id ^ "' already defined"))
        else M.add id {s_name=id; s_ordered_fields = [];
          s_fields=(Hashtbl.create 5); s_size=0} structures
  | PDfunction _ -> structures

let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> s.s_size
  | t -> raise (Anomaly
      ("evaluating size of '" ^ printable_type t ^ "'"))

(* recursively computes size and offset of a structure and
   its fields *)
let rec define_sizeof s =
  s.s_size <- List.fold_left define_ofs 0 s.s_ordered_fields

and define_ofs acc ({f_typ} as field) =
  field.f_ofs <- acc; if sizeof f_typ = 0 
    then begin match f_typ with
      | Tstruct s -> define_sizeof s
      | t -> () (* cannot happen *)
    end;
    acc + (sizeof f_typ)

(* returns a list of typed parameters for a given function, as a list of vars *)
let rec build_parameters structures f_name used_names counter = function
  | [] -> []
  | ({id; loc}, ptyp) :: q -> if List.mem id used_names
      then raise (Error (loc, "function '" ^ f_name ^
        "': redefinition of parameter '" ^ id ^ "'"))
      else begin
        let typ = find_type structures ptyp in
        let v = new_var id loc typ ~used:true in v.v_addr <- 8 * counter;
        v :: build_parameters structures f_name (id :: used_names) (counter + 1) q
      end

(* types and adds a list of fields to a given structure, returns the ordered
   list of all fields. *)
let rec add_fields structure_context structure used_names = function
  | [] -> []
  | ({id; loc}, ptyp) :: q -> if List.mem id used_names
      then raise (Error (loc, "structure '" ^ structure.s_name ^
        "': redefinition of field '" ^ id ^ "'"))
      else begin
        let typ = find_type structure_context ptyp in
        let field = {f_name=id; f_typ=typ; f_ofs=0} in
        Hashtbl.add structure.s_fields id field;
        field :: add_fields structure_context structure (id :: used_names) q
      end


(* 2. declare functions and type fields *)
(* only creates function mappings while editing structure fields *)
let phase2 structures functions = function
  | PDfunction {pf_name={id; loc}; pf_params=pl; pf_typ=tyl} ->
      if id = "main" && pl = [] && tyl = [] then found_main := true;
      if M.mem id functions
        then raise (Error (loc, "function '" ^ id ^ "' already defined"));
  (* why 2? both return address and previous %rbp value are on the stack *)
      let fn_params = build_parameters structures id [] 2 pl in
      let fn_typ = List.map (find_type structures) tyl in
      M.add id {fn_name=id; fn_params; fn_typ} functions

  | PDstruct {ps_name = {id; _}; ps_fields} ->
      let s = M.find id structures in
      s.s_ordered_fields <- add_fields structures s [] ps_fields;
      functions

exception Cyclic of string * string

let cyclic_definition_detection structures =
  let marks = Hashtbl.create 5 and fin = Hashtbl.create 5 in
  let rec dfs {s_name; s_fields} = if not (Hashtbl.mem fin s_name) then begin
    if Hashtbl.mem marks s_name
      then raise (Cyclic (s_name, "has field of type '" ^ s_name ^ "'"))
      else try
        Hashtbl.add marks s_name ();
        Hashtbl.iter (fun s -> function
          | {f_typ=Tstruct structure} -> dfs structure
          | _ -> ()
        ) s_fields;
        Hashtbl.add fin s_name ()
      with
        | Cyclic (orig, trail) when orig = s_name ->
            raise (Error (dummy_loc, "cyclic definition:\n\tstructure '" ^ s_name ^ "' " ^ trail))
        | Cyclic (orig, trail) ->
            raise (Cyclic (orig, "has field of type '" ^ s_name ^ "'\n\twhich " ^ trail))
  end in
  M.iter (fun s -> dfs) structures
        

(* 3. type check function bodies *)
let decl structures functions = function
  | PDfunction {pf_name={id; loc}; pf_body} ->
    let f = M.find id functions in
    let env = Env.new_env functions structures f in
    let e, env' = expr env pf_body in
    if f.fn_typ = [] || env'.returns
      then TDfunction (f, e)
      else raise (Error (loc, "missing return statements for function '" ^ id ^ "'"))

  | PDstruct {ps_name={id}} ->
    let s = M.find id structures in
    define_sizeof s;
    (* debug to print information on structures *)
    if !debug then begin
      print_string ("In typing : structure '" ^ id ^ "' has size "
        ^ string_of_int (sizeof (Tstruct s)) ^ "\n");
      List.iter (fun {f_name; f_ofs} ->
        print_string ("\tfield '" ^ f_name ^ "' has offset "
          ^ string_of_int f_ofs ^ "\n")) s.s_ordered_fields
    end;
    TDstruct s

(* local variables (functions, structures) are used to represent context *)
let file ~debug:b (imp, dl) =
  debug := b;
  fmt_imported := imp;

  let structures = List.fold_left phase1 M.empty dl in
  if !debug then print_string "PHASE 1 DONE\n";
  let functions = List.fold_left (phase2 structures) M.empty dl in
  if !debug then print_string "PHASE 2 DONE\n";
  
  if not !found_main then raise (Error (dummy_loc, "missing method main"));
  cyclic_definition_detection structures;

  let dl = List.map (decl structures functions) dl in
  Env.check_unused (); 
  if imp && not !fmt_used then raise (Error (dummy_loc, "fmt imported but not used"));
  if !debug then print_string "PHASE 3 DONE\n";
  dl
