type name = Name of string

type dname = DName of string

type lname = LName of string

type tname = TName of string



let namet tname = let TName name = tname in name
let namel lname = let LName name = lname in name
let named dname = let DName name = dname in name
let namen nname = let Name name = nname in name




















