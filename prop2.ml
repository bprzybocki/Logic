type prop_fm = False
             | True
             | Var of string
             | Not of prop_fm
             | And of prop_fm * prop_fm
             | Or of prop_fm * prop_fm
             | Imp of prop_fm * prop_fm
             | Iff of prop_fm * prop_fm
             | None;;

let rec polish (fm : prop_fm) : string =
        match fm with
          False -> "0"
        | True -> "1"
        | Var p -> p
        | Not p -> "N"^(polish p)
        | And(p,q) -> "K"^(polish p)^(polish q)
        | Or(p,q) -> "A"^(polish p)^(polish q)
        | Imp(p,q) -> "C"^(polish p)^(polish q)
        | Iff(p,q) -> "E"^(polish p)^(polish q)
        | None -> "";;

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
        | Iff(p,q) -> (eval p v) = (eval q v)
        | None -> false;;

let rec dual (fm : prop_fm) : prop_fm =
        match fm with
          False -> True
        | True -> False
        | Var p -> fm
        | Not p -> Not(dual p)
        | And(p,q) -> Or(dual p, dual q)
        | Or(p,q) -> And(dual p, dual q)
        | _ -> None;;

let rec cnf_to_list (fm : prop_fm) : prop_fm list list =
        match fm with
          Var p -> [[Var p]]
        | Not p -> [[Not p]]
        | And(p,q) -> cnf_to_list p @ cnf_to_list q
        | Or(p,q) -> [List.hd (cnf_to_list p) @ List.hd (cnf_to_list q)]
        | _ -> [[None]];;

let rec dnf_to_list (fm : prop_fm) : prop_fm list list =
        match fm with
          Var p -> [[Var p]]
        | Not p -> [[Not p]]
        | And(p,q) -> [List.hd (cnf_to_list p) @ List.hd (cnf_to_list q)]
        | Or(p,q) -> cnf_to_list p @ cnf_to_list q
        | _ -> [[None]];;

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
        if forall (fun cl -> length cl != 1) clauses then [[None]] else
        let u = List.hd (find (fun cl -> length cl = 1) clauses) in
        let u' = negate u in
        let clauses1 = filter (fun cl -> not (mem u cl)) clauses in
        image (fun cl -> subtract cl [u']) clauses1;;

let affirmative_negative_rule (clauses : prop_fm list list) : prop_fm list list =
        let neg',pos = partition negative (unions clauses) in
        let neg = image negate neg' in
        let pos_only = subtract pos neg and neg_only = subtract neg pos in
        let pure = union pos_only (image negate neg_only) in
        if pure = [] then [[None]]  else
        filter (fun cl -> intersect cl pure = []) clauses;;

let posneg_count (cls : prop_fm list list) (l : prop_fm) : int =
        let m = length(filter (mem l) cls)
        and n = length(filter (mem (negate l)) cls) in
        m + n;;

let rec dpll (clauses : prop_fm list list) : bool option =
        if clauses = [[None]] then None else
        if clauses = [] then Some true else
        if mem [] clauses then Some false else
        let dp1 = dpll(one_literal_rule clauses) in
        if dp1 != None then dp1 else
        let dp2 = dpll(affirmative_negative_rule clauses) in
        if dp2 != None then dp2 else
        let pvs = filter positive (unions clauses) in
        let p = maximize (posneg_count clauses) pvs in
        Some (dpll (insert [p] clauses) = Some true  ||
        dpll (insert [negate p] clauses) = Some true);;

let dpllsat (fm : prop_fm) : bool option = dpll(cnf_to_list (cnf fm));;

let dplltaut (fm : prop_fm) : bool option =
        match dpllsat(Not fm) with
          Some true -> Some false
        | Some false -> Some true
        | None -> None;;

type trailmix = Guessed | Deduced;;

let unassigned =
  let litabs p = match p with Not q -> q | _ -> p in
  fun cls trail -> subtract (unions(image (image litabs) cls))
                            (image (litabs ** fst) trail);;

let rec unit_subpropagate (cls,fn,trail) =
  let cls' = map (filter ((not) ** defined fn ** negate)) cls in
  let uu = function [c] when not(defined fn c) -> [c] | _ -> [] in
  let newunits = unions(map uu cls') in
  if newunits = [] then (cls',fn,trail) else
  let trail' = itlist (fun p t -> (p,Deduced)::t) newunits trail
  and fn' = itlist (fun u -> (u |-> ())) newunits fn in
  unit_subpropagate (cls',fn',trail');;

let unit_propagate (cls,trail) =
  let fn = itlist (fun (x,_) -> (x |-> ())) trail undefined in
  let cls',fn',trail' = unit_subpropagate (cls,fn,trail) in cls',trail';;

let rec backtrack trail =
  match trail with
    (p,Deduced)::tt -> backtrack tt
  | _ -> trail;;

let rec backjump cls p trail =
  match backtrack trail with
    (q,Guessed)::tt ->
        let cls',trail' = unit_propagate (cls,(p,Guessed)::tt) in
        if mem [] cls' then backjump cls p tt else trail
  | _ -> trail;;

let rec dplb cls trail =
  let cls',trail' = unit_propagate (cls,trail) in
  if mem [] cls' then
    match backtrack trail with
      (p,Guessed)::tt ->
        let trail' = backjump cls p tt in
        let declits = filter (fun (_,d) -> d = Guessed) trail' in
        let conflict = insert (negate p) (image (negate ** fst) declits) in
        dplb (conflict::cls) ((negate p,Deduced)::trail')
    | _ -> false
  else
    match unassigned cls trail' with
      [] -> true
    | ps -> let p = maximize (posneg_count cls') ps in
            dplb cls ((p,Guessed)::trail');;

let dplbsat fm = dplb (cnf_to_list (cnf fm)) [];;

let dplbtaut fm = not(dplbsat(Not fm));;
