type prop_fm = False
             | True
             | Var of string
             | Not of prop_fm
             | And of prop_fm * prop_fm
             | Or of prop_fm * prop_fm
             | Imp of prop_fm * prop_fm
             | Iff of prop_fm * prop_fm;;

let rec polish (fm : prop_fm) : string =
        match fm with
          False -> "0"
        | True -> "1"
        | Var p -> p
        | Not p -> "N"^(polish p)
        | And(p,q) -> "K"^(polish p)^(polish q)
        | Or(p,q) -> "A"^(polish p)^(polish q)
        | Imp(p,q) -> "C"^(polish p)^(polish q)
        | Iff(p,q) -> "E"^(polish p)^(polish q);;

let psimplify1 (fm : prop_fm) : prop_fm =
        match fm with
          Not False -> True
        | Not True -> False
        | Not(Not p) -> p
        | And(p,False) | And(False,p) -> False
        | And(p,True) | And(True,p) -> p
        | Or(p,False) | Or(False,p) -> p
        | Or(p,True) | Or(True,p) -> True
        | Imp(False,p) | Imp(p,True) -> True
        | Imp(True,p) -> p
        | Imp(p,False) -> Not p
        | Iff(p,True) | Iff(True,p) -> p
        | Iff(False,False) -> True
        | Iff(p,False) | Iff(False,p) -> Not p
        | _ -> fm;;

let rec psimplify (fm : prop_fm) : prop_fm =
        match fm with
          Not p -> psimplify1 (Not(psimplify p))
        | And(p,q) -> psimplify1 (And(psimplify p,psimplify q))
        | Or(p,q) -> psimplify1 (Or(psimplify p, psimplify q))
        | Imp(p,q) -> psimplify1 (Imp(psimplify p, psimplify q))
        | Iff(p,q) -> psimplify1 (Iff(psimplify p, psimplify q))
        | _ -> fm;;

let rec nnf (fm : prop_fm) : prop_fm =
        match fm with
          And (p,q) -> And(nnf p,nnf q)
        | Or(p,q) -> Or(nnf p,nnf q)
        | Imp(p,q) -> Or(nnf(Not p),nnf q)
        | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
        | Not(Not p) -> nnf p
        | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
        | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
        | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
        | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
        | _ -> fm;;

let nnf (fm : prop_fm) : prop_fm = nnf(psimplify fm);;

let rec distrib_dnf (fm : prop_fm) : prop_fm =
        match fm with
          And(p,Or(q,r)) -> Or(distrib_dnf(And(p,q)),distrib_dnf(And(p,r)))
        | And(Or(p,q),r) -> Or(distrib_dnf(And(p,r)),distrib_dnf(And(q,r)))
        | _ -> fm;;

let rec rawdnf (fm : prop_fm) : prop_fm =
        match fm with
          And(p,q) -> distrib_dnf(And(rawdnf p,rawdnf q))
        | Or(p,q) -> Or(rawdnf p,rawdnf q)
        | _ -> fm;;

let dnf (fm : prop_fm) : prop_fm = rawdnf (nnf fm);;

let rec distrib_cnf (fm : prop_fm) : prop_fm =
        match fm with
          Or(p,And(q,r)) -> And(distrib_cnf(Or(p,q)),distrib_cnf(Or(p,r)))
        | Or(And(p,q),r) -> And(distrib_cnf(Or(p,r)),distrib_cnf(Or(q,r)))
        | _ -> fm;;

let rec rawcnf (fm : prop_fm) : prop_fm =
        match fm with
          Or(p,q) -> distrib_cnf(Or(rawcnf p,rawcnf q))
        | And(p,q) -> And(rawcnf p,rawcnf q)
        | _ -> fm;;

let cnf (fm : prop_fm) : prop_fm = rawcnf (nnf fm);;

let rec eval (fm : prop_fm) (v : string -> bool) : bool =
        match fm with
          False -> false
        | True -> true
        | Var p -> v(p)
        | Not p -> not(eval p v)
        | And(p,q) -> (eval p v) && (eval q v)
        | Or(p,q) -> (eval p v) || (eval q v)
        | Imp(p,q) -> not(eval p v) || (eval q v)
        | Iff(p,q) -> (eval p v) = (eval q v);;

let rec dual (fm : prop_fm) : prop_fm =
        match fm with
          False -> True
        | True -> False
        | Var p -> fm
        | Not p -> Not(dual p)
        | And(p,q) -> Or(dual p, dual q)
        | Or(p,q) -> And(dual p, dual q)
        | _ -> failwith "Formula involves connectives ==> or <=>";;

let rec cnf_to_list (fm : prop_fm) : prop_fm list list =
        match fm with
          Var p -> [[Var p]]
        | Not p -> [[Not p]]
        | And(p,q) -> cnf_to_list p @ cnf_to_list q
        | Or(p,q) -> [List.hd (cnf_to_list p) @ List.hd (cnf_to_list q)]
        | _ -> failwith "Formula not in CNF";;

let rec dnf_to_list (fm : prop_fm) : prop_fm list list =
        match fm with
          Var p -> [[Var p]]
        | Not p -> [[Not p]]
        | And(p,q) -> [List.hd (cnf_to_list p) @ List.hd (cnf_to_list q)]
        | Or(p,q) -> cnf_to_list p @ cnf_to_list q
        | _ -> failwith "Formula not in DNF";;

let negative (lit : prop_fm) : bool =
        match lit with
          Not p -> true
        | _ -> false;;

let positive (lit : prop_fm) : bool = not(negative lit);;

let negate (lit : prop_fm) : prop_fm =
        match lit with
          Not p -> p
        | p -> Not p;;

let trivial (lits : prop_fm list) : bool =
        let pos,neg = partition positive lits in
        intersect pos (image negate neg) <> [];;

let cnf_to_list (fm : prop_fm) : prop_fm list list =
        let list1 = filter (non trivial) (cnf_to_list fm) in
        let list2 = image setify list1 in
        setify list2;;

let dnf_to_list (fm : prop_fm) : prop_fm list list =
        let list1 = filter (non trivial) (dnf_to_list fm) in
        let list2 = image setify list1 in
        setify list2;;

let one_literal_rule (clauses : prop_fm list list) : prop_fm list list =
        let u = List.hd (find (fun cl -> length cl = 1) clauses) in
        let u' = negate u in
        let clauses1 = filter (fun cl -> not (mem u cl)) clauses in
        image (fun cl -> subtract cl [u']) clauses1;;

let affirmative_negative_rule (clauses : prop_fm list list) : prop_fm list list =
        let neg',pos = partition negative (unions clauses) in
        let neg = image negate neg' in
        let pos_only = subtract pos neg and neg_only = subtract neg pos in
        let pure = union pos_only (image negate neg_only) in
        if pure = [] then failwith "affirmative_negative_rule" else
        filter (fun cl -> intersect cl pure = []) clauses;;

let posneg_count (cls : prop_fm list list) (l : prop_fm) : int =
        let m = length(filter (mem l) cls)
        and n = length(filter (mem (negate l)) cls) in
        m + n;;

let rec dpll clauses =
        if clauses = [] then true else if mem [] clauses then false else
        try dpll(one_literal_rule clauses) with Failure _ ->
        try dpll(affirmative_negative_rule clauses) with Failure _ ->
        let pvs = filter positive (unions clauses) in
        let p = maximize (posneg_count clauses) pvs in
        dpll (insert [p] clauses) || dpll (insert [negate p] clauses);;

let dpllsat (fm : prop_fm) : bool = dpll(cnf_to_list (cnf fm));;

let dplltaut (fm : prop_fm) : bool = not(dpllsat(Not fm));;
