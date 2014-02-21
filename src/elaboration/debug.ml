
  (* and type_definition = *)
  (*   | TypeDef of position * mltypekind * tname * datatype_definition *)
  (*   | ExternalType of position * tnames * tname * string *)

  (* and datatype_definition = *)
  (*   | DAlgebraic of (position * dname * tnames * mltype) list *)
  (*   | DRecordType of tnames * (position * lname * mltype) list *)


    (* | TypeDefs of position * type_definition list *)

open Format
open XAST
open Types
open Name


open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment



let rec string_of_type t =
  match t with
  | TyVar (_, TName tname) -> Format.sprintf "%s" tname
  | TyApp (_, TName tname, ts) when tname = "->" || tname = "*"->
    "(" ^ (String.concat (" " ^ tname ^ " ") (List.map (string_of_type) ts)) ^ ")"
  | TyApp (_, TName tname, ts) ->
      let params = begin match ts with
        [] -> "" | [p] -> (string_of_type p) ^ " "
      | l -> "(" ^ (String.concat ", " (List.map (string_of_type) ts)) ^ ") "
      end in
      Format.sprintf "%s%s" params tname

and print_instance_definition fmt i =
  Format.fprintf fmt "Inst : %s " (let TName s = i.instance_class_name in s);
  Format.fprintf fmt "%s " (let TName s =  i.instance_index in s);
  Format.fprintf fmt "(%s) "
    (String.concat ", " (List.map (
      fun (ClassPredicate (TName s1, TName s2)) -> s1 ^ " " ^ s2 )
                           i.instance_typing_context));
  Format.fprintf fmt "(%s) "
    (String.concat ", " (List.map (
      fun (TName s) -> s) i.instance_parameters));
  Format.fprintf fmt "(%s)@\n"
    (String.concat ", " (List.map (fun (RecordBinding (LName s, _)) -> s) i.instance_members))


and print_class_definition c =
  Format.printf "%s %s (%s) \n@\n"
    (let TName s = c.class_name in s)
    (let TName s = c.class_parameter in s)
    (String.concat ", " (List.map (fun (_, LName s, t) ->
      s ^ ":" ^ (string_of_type t)) c.class_members))

(* type kind = *)
(*   | KStar *)
(*   | KArrow of kind * kind *)
let rec print_kind fmt = function
| KStar -> fprintf fmt "KStar"
| KArrow (k1, k2) -> fprintf fmt "%a %a" print_kind k1 print_kind k2


let str_sep sep f l =
  (String.concat sep (List.map f l))

let print_datatype_def fmt = function
| DAlgebraic _ -> fprintf fmt "ADT"
| DRecordType (tnames, members) ->
    fprintf fmt "(%s) {\n%s\n}\n"
      (String.concat ", " (List.map (fun (TName name) -> name) tnames))
      (String.concat ";\n" (List.map (fun (_, LName name, ty) ->
        sprintf "%s: %s" name (string_of_type ty)
       ) members))


let print_typedef fmt = function
| TypeDef (_, kind, TName name, dty) ->
    fprintf fmt "%a %s %a" print_kind kind name print_datatype_def dty
| ExternalType (_, tnames, TName name, string) -> ()


let print_typedefs fmt (TypeDefs (_, tds)) =
  List.iter (fprintf fmt "%a@\n" print_typedef) tds



let string_of_expr e = ASTio.(XAST.(to_string pprint_expression e))


let print_value_def fmt defs =
  List.iter (
    fun (ValueDef (_, tnames, class_predicates, (Name name, ty), expression))
  ->
    fprintf fmt "%s, (%s) (%s : %s) = %s@\n"
      (str_sep ", " (fun (TName name) -> name) tnames)
      (str_sep ", " (fun (ClassPredicate (TName t1, TName t2)) ->
        sprintf "%s * %s" t1 t2) class_predicates)
      name
      (string_of_type ty)
      (string_of_expr expression)
  ) defs


let print_value_bindings fmt = function
| BindValue (_, defs) -> print_value_def fmt defs
| BindRecValue (_, value_definitions) -> ()
| ExternalValue (_, tnames, binding, string) -> ()
