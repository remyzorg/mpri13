(** Name scopes. *)

(** Program identifiers. *)
type name = Name of string

(** Data constructor identifiers. *)
type dname = DName of string

(** Label identifiers. *)
type lname = LName of string

(** Type identifiers. *)
type tname = TName of string


val namet : tname -> string
val namel : lname -> string
val named : dname -> string
val namen : name -> string
