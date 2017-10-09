datatype atom = Var of string | Const of string;


datatype fact = Fact of string * atom list;


Fact("Likes", [Const("Kathy"), Const("Cars")]);
Fact("Likes", [Const("Maisie"), Const("Cars")]);
Fact("Likes", [Const("Maisie"), Const("Oatmeal")]);
Fact("Likes", [Const("Stephanie"), Const("Michigan")]);
Fact("Likes", [Var("x"), Const("Chocolate")]);
Fact("Likes", [Const("Harvey"), Var("x")]);




datatype substitution = Failure | Sub of (string * atom) list;


exception failedLookup;


fun lookup(v, []) = raise failedLookup
  | lookup(v, (w, x)::rest) = if v = w then x else lookup(v, rest);


fun unifyAtom(Const(c), Const(d), subst) = if c = d then subst else Failure
  | unifyAtom(Var(v), y, subst) = unifyVar(v, y, subst)
  | unifyAtom(x, Var(w), subst) = unifyVar(w, x, subst)


and unifyVar(v, y, s as Sub(subs)) =
    (unifyAtom(lookup(v, subs), y, s)
     handle failedLookup =>
            (case y of
                 Var(w) => (unifyAtom(Var(v), lookup(w, subs), s)
                            handle failedLookup =>
                                   if v = w then Failure else Sub((v, y)::subs))
               | Const(s) => Sub((v, Const(s))::subs)))
  | unifyVar(_,_,_) = Failure;


fun unifyList(_, _, Failure) = Failure
  | unifyList(xFst::xRest, yFst::yRest, subst) =
       unifyList(xRest, yRest, unifyAtom(xFst, yFst, subst))
  | unifyList([], [], subst) = subst
  | unifyList(_, _, _) = Failure;


fun unifyFact(Fact(xOp, xArgs), Fact(yOp, yArgs), subst) =
    if xOp = yOp then unifyList(xArgs, yArgs, subst) 
                      else Failure;


(* samples *)
unifyFact(Fact("Likes", [Const("Stephanie"), Var("x")]),
          Fact("Likes", [Const("Stephanie"), Const("Michigan")]), Sub([]));


unifyFact(Fact("Likes", [Const("Stephanie"), Var("c")]),
          Fact("Likes", [Var("y"), Const("Chocolate")]), Sub([]));


unifyFact(Fact("Likes", [Const("Stephanie"), Var("x")]),
          Fact("Likes", [Const("Maisie"), Const("Oatmeal")]), Sub([]));




datatype rule = Rule of fact list * fact;


(* samples *)
Rule([Fact("Likes", [Var("x"), Const("Cars")])], 
     Fact("Knows", [Var("x"), Const("Jim")]));


Rule([Fact("Likes", [Var("x"), Const("Oatmeal")])], 
     Fact("Knows", [Var("x"), Const("Jim")]));


Rule([Fact("Likes", [Var("x"), Const("Cars")]),
      Fact("Likes", [Var("x"), Const("Oatmeal")])], 
     Fact("Knows", [Var("x"), Const("Fred")]));


val factList = ref [Fact("Knows", [Const("John"), Const("Jane")]),
                    Fact("Knows", [Var("y"), Const("Bill")])];
val ruleList = ref([]: rule list);


val factList = 
  ref [Fact("Likes", [Const("Kathy"), Const("Cars")]),
   Fact("Likes", [Const("Maisie"), Const("Cars")]),
   Fact("Likes", [Const("Maisie"), Const("Oatmeal")]),
   Fact("Likes", [Const("Stephanie"), Const("Michigan")]),
   Fact("Likes", [Var("x"), Const("Chocolate")]),
   Fact("Likes", [Const("Harvey"), Var("x")])];
val ruleList =
  ref [Rule([Fact("Likes", [Var("x"), Const("Cars")])], 
        Fact("Knows", [Var("x"), Const("Jim")])),
   Rule([Fact("Likes", [Var("x"), Const("Oatmeal")])], 
        Fact("Knows", [Var("x"), Const("Jim")])),
   Rule([Fact("Likes", [Var("x"), Const("Cars")]),
         Fact("Likes", [Var("x"), Const("Oatmeal")])], 
        Fact("Knows", [Var("x"), Const("Fred")]))];




(* Some fragments from the text: 
and resolve(goal, subst) =
    resolveFact(goal, !factList, subst)@
    resolveRule(goal, !ruleList, subst);




val idGen = ref 0;


fun makeUnique(v) = (idGen := !idGen + 1;
                     v ^ Int.toString(!idGen));


and resolveSubstList(goals, []) = []
  | resolveSubstList(goals, subst::rest) =
    resolveGoalList(goals, subst)@resolveSubstList(goals, rest)


fun tellFact(fact) = factList := fact::!factList;
fun tellRule(rule) = ruleList := rule::!ruleList;


fun deepLookup(v, subs) = 
    case lookup(v, subs) of
        Const(c) => c
      | Var(vv) => deepLookup(vv, subs);


fun getVars([]) = []
  | getVars(Const(c)::rest) = getVars(rest)
  | getVars(Var(v)::rest) = v::getVars(rest);


fun printResult([], _) = print(";\n")
  | printResult(_, Failure) = print("fail")  (* shouldn't happen *)
  | printResult(x::rest, Sub(subs)) = 
    (print(x ^ "=" ^ deepLookup(x, subs) ^ " ");
     printResult(rest, Sub(subs)));


fun printResults(vars, []) = print(".\n")
  | printResults(vars, sub::rest) = 
    (printResult(vars, sub); printResults(vars, rest));




fun ask(Fact(oper, args)) = 
    let val results = resolve(Fact(oper, args), Sub([]));
        val vars = getVars(args);
    in if results = [] then print("no\n")
                            else printResults(vars, results)
    end;


End fragments *)




(* The whole system (besides the datatypes and basic functions from
   the beginning of the file) starts here.... with parts you need to write 
   in the project problems removed. *)


exception substitutionFailure
(*
fun subAtom(_, Failure) = raise substitutionFailure
  | subAtom(Var(v), Sub(subs)) = 
    (lookup(v, subs) handle failedLookup => Var(v))
  | subAtom(Const(c), subst) = Const(c)


and subFact(_, Failure) = raise substitutionFailure
  | subFact(Fact(oper, args), subst) = Fact(oper, subList(args, subst))


and subList(_, Failure) = raise substitutionFailure
  | subList(fst::rest, subst) = subAtom(fst, subst)::subList(rest, subst);
*)


val idGen = ref 0;


fun makeUnique(v) = (idGen := !idGen + 1;
                     v ^ Int.toString(!idGen));


fun standardizeAtom(Var(v), replacements) =
    ((lookup(v, replacements), replacements)
     handle failedLookup => 
            let val newVar = makeUnique(v);
            in (Var(newVar), (v, Var(newVar))::replacements)
            end)
  | standardizeAtom (c, replacements) = (c, replacements)


and standardizeFact(Fact(s, atoms), replacements) =
    let val (newAtoms, newReplacements) =
            standardizeAtomList(atoms, replacements)
    in (Fact(s, newAtoms), newReplacements) end


and standardizeAtomList([], replacements) = ([], replacements)
  | standardizeAtomList(a::rest, replacements) =
    let val (newA, replacements2) = standardizeAtom(a, replacements);
         val (newRest, replacements3) = standardizeAtomList(rest, replacements2);
    in (newA::newRest, replacements3)
    end


and standardizeFactList([], replacements) = ([], replacements)
  | standardizeFactList(f::rest, replacements) = 
    let val (newF, replacements2) = standardizeFact(f, replacements);
        val (newRest, replacements3) = standardizeFactList(rest, replacements2);
    in (newF::newRest, replacements3)
    end


and standardizeRule(Rule(premises, conclusion)) =
    let val (newPremises, newReplacements) = 
            standardizeFactList(premises, []);
    in Rule(newPremises, #1(standardizeFact(conclusion, newReplacements)))
    end; 




(* For Project 5.A *)
fun resolveFact(goal, fact::rest, subst) =
    (case unifyFact(goal, #1(standardizeFact(fact, [])), subst) of
         Failure => resolveFact(goal, rest, subst)
       | Sub(s) => Sub(s) :: resolveFact(goal, rest, subst))
  | resolveFact(goal, [], subst) = []


(* For Project 5.B *)
and resolveRule(goal, r::rest, subst)  =
    let val Rule(premises, conclus) = standardizeRule(r)
    in
        case unifyFact(goal, conclus, subst) of
            Failure => resolveRule(goal, rest, subst)
          | subst2 => 
            (case resolveGoalList(premises, subst2) of
                 [] => resolveRule(goal, rest, subst)
               | substs => subst2 :: resolveRule(goal, rest, subst)) 
    end
  | resolveRule(goal, [], subst) = []


(* For Project 5.C *)
and resolveGoalList(goal::rest, subst) =   
    (case resolve(goal, subst) of
        [] => []
      | substs => resolveSubstList(rest, substs))
  | resolveGoalList([], subst) = [subst]


and resolveSubstList(goals, []) = []        
  | resolveSubstList(goals, subst::rest) =
    resolveGoalList(goals, subst)@resolveSubstList(goals, rest)


and resolve(goal, subst) =
    resolveFact(goal, !factList, subst)@
    resolveRule(goal, !ruleList, subst);



fun tellFact(fact) = factList := fact:: !factList;
fun tellRule(rule) = ruleList := rule:: !ruleList;

fun getFact(a::b::c::rest) = if (Char.isUpper(String.sub(b, 0)) andalso Char.isUpper(String.sub(c, 0)))
					  then Fact(a, [Const(b), Const(c)])
					  else if (Char.isLower(String.sub(b, 0)) andalso Char.isLower(String.sub(c, 0)))
					  then Fact(a, [Var(b), Var(c)])
					  else if (Char.isUpper(String.sub(b, 0)) andalso Char.isLower(String.sub(c, 0)))
					  then Fact(a, [Const(b), Var(c)])
					  else Fact(a, [Var(b), Const(c)]);
					  
  
fun getFactList(a::b::c::[]) = []
  | getFactList(a::b::c::rest) = getFact(a::b::c::[]) :: getFactList(rest)
  | getFactList(rest) = [];   (*shouldn't happen*)
  
fun getLastFact(a::b::c::[]) = getFact(a::b::c::[])
  | getLastFact(a::b::c::rest) = getLastFact(rest)
  | getLastFact(rest) = Fact("none", [Var("none"), Const("none")]);   (*shouldn't happen*)
					  
fun getRule(wordList) = 
    let val factList = getFactList(wordList)
        val lastFact = getLastFact(wordList)
    in
        Rule(factList, lastFact)
    end;

fun tell(info) = 
	let val wordList = String.tokens(fn(x) => not(Char.isAlpha(x)))(info); 
	in
	    case List.length(wordList) of
	    3 => tellFact(getFact(wordList)) 
	  | _ => tellRule(getRule(wordList))
	end;

fun getVars([]) = []
  | getVars(Const(c)::rest) = getVars(rest)
  | getVars(Var(v)::rest) = v::getVars(rest);


fun atomToString(Var(v)) = v
  | atomToString(Const(c)) = c;


fun deepLookup(v, subs) = 
    case lookup(v, subs) of
        Const(c) => c
      | Var(vv) => deepLookup(vv, subs);


fun printResult([], _) = print(";\n")
  | printResult(_, Failure) = print("fail")  (* shouldn't happen *)
  | printResult(x::rest, Sub(subs)) = 
    (print(x ^ "=" ^ deepLookup(x, subs) ^ " ");
     printResult(rest, Sub(subs)));


fun printResults(vars, []) = print(".\n")
  | printResults(vars, sub::rest) = 
    (printResult(vars, sub); printResults(vars, rest));


fun ask(Fact(oper, args)) = 
    let val results = resolve(Fact(oper, args), Sub([]));
        val vars = getVars(args);
    in if results = [] then print("no\n")
                            else printResults(vars, results)
    end;

fun improvedAsk(info) = 
	let val fact = getFact(String.tokens(fn(x) => not(Char.isAlpha(x)))(info)); 
	in
	    ask(fact)
	end;

val r = Rule([Fact("Likes", [Var("y"), Const("IceCream")])],
             Fact("Knows", [Var("y"), Const("Larry")]));


val r2 = Rule([Fact("Likes", [Var("x"), Const("IceCream")])],
             Fact("Knows", [Var("y"), Const("Larry")]));


factList := [Fact("Knows", [Var("x"), Const("Jane")]),
             Fact("Likes", [Const("John"), Const("IceCream")])];


ruleList := [Rule([Fact("Likes", [Var("y"), Const("IceCream")])],
             Fact("Knows", [Var("y"), Const("Larry")]))];


resolve(Fact("Knows", [Const("John"), Var("x")]), Sub([]));

ask(Fact("Knows", [Const("John"), Var("x")]));

(* Testing for Project 5.D *)
tell("Knows(John, Kim)");
tell("Likes(Kim, Candy)");
tell("Likes(Kim, Cars)");
tell("Likes(Kim, Oatmeal)");
tell("[Likes(x, Candy)], Likes(x, Fruit)");
tell("[Likes(x, Cars), Likes(x, Oatmeal)], Knows(x, Fred)");

improvedAsk("Knows(John,x)");
improvedAsk("Likes(Kim, Bikes)");
improvedAsk("Likes(Kim, Candy)");
improvedAsk("Likes(Kim, x)"); 
improvedAsk("Knows(Kim, x)");

(* For Project 5.E *)

tell("Serves(EastGrille, Halibut)");
tell("Serves(FishKing, Tofu)");
improvedAsk("Serves(EastGrille,x)");

tell("[Serves(x, Halibut)], CanEatAt(Angie, x)");
improvedAsk("CanEatAt(Angie, EastGrille)");
improvedAsk("CanEatAt(Angie, FishKing)");

improvedAsk("CanEatAt(Angie, x)");

(*

tell("Serves(EastGrille, Hamburgers)");
tell("Serves(EastGrille, Halibut)");
tell("Serves(Bertie's, Hamburgers)");
tell("Serves(CityTavern, Hamburgers)");
tell("Serves(CityTavern, Tofu)");
tell("Serves(FishKing, Halibut)");
tell("Has(Bertie's, Patio)");
tell("Has(FishKing, Patio)");
tell("Requires(CityTavern, Shoes)");
tell("Requires(FishKing, Shoes)");
tell("Requires(EastGrille, Ties)");

tell("[Serves(x, Hamburgers)], Serves(x, Fries)");
tell("[Serves(x, Halibut)], CanEatAt(Angie, x)");
tell("[Serves(x, Fries)], CanEatAt(Brad, x)");
tell("[Serves(x, Tofu)], CanEatAt(Casey, x)");
tell("[Requires(x, Ties)], Requires(x, Shoes)");
tell("[Requires(x, Shoes)], CanEatAt(Casey, x)");
tell("[Requires(x, Ties)], CanEatAt(Dora, x)");
tell("[CanEatAt(Angie, x)], CanEatAt(Evert, x)");
tell("[Has(x, Patio)], CanEatAt(Fuchsia, x)");

improvedAsk("CanEatAt(Angie, x)");
*)


