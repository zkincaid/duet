open Printf;;

(* This is the type of the contents of a weight.
 *   It is a black box as far as this OCaml code is concerned;
 *    its contents are only manipulated by the C++ code *)
type weight;;

type regExp =
    | Zero
    | One
    | Var of int
    | Weight of weight
    | Project of regExp
    | Plus of regExp * regExp
    | Dot of regExp * regExp
    | Kleene of regExp * int (* this int is a unique key for this star *)
    | Detensor of regExp * regExpT

and regExpT =
    | ZeroT
    | OneT
    | VarT of int
    | ProjectT of regExpT
    | PlusT of regExpT * regExpT
    | DotT of regExpT * regExpT
    | KleeneT of regExpT * int (* this int is a unique key for this star *)
    | Tensor of regExp * regExp
;;

(* let try_icra_regexp () = 42;; *)

(* let _ = Callback.register "try_icra_regexp" try_icra_regexp;;          *)

(* ---- external functions ---- *)
(* These functions are defined externally (in C) and are called in this OCaml file. *)

external evalKleeneSemElemT : weight -> int -> weight = "IRE_evalKleeneSemElemT"
external evalKleeneSemElem : weight -> int -> weight = "IRE_evalKleeneSemElem"
external evalPlusSemElemT : weight -> weight -> weight = "IRE_evalPlusSemElemT"
external evalPlusSemElem : weight -> weight -> weight = "IRE_evalPlusSemElem"
external evalDotSemElemT : weight -> weight -> weight = "IRE_evalDotSemElemT"
external evalDotSemElem : weight -> weight -> weight = "IRE_evalDotSemElem"
external evalProjectSemElemT : weight -> weight = "IRE_evalProjectSemElemT"
external evalProjectSemElem : weight -> weight = "IRE_evalProjectSemElem"
external evalVarSemElem : int -> weight = "IRE_evalVarSemElem"
external evalVarSemElemT : int -> weight = "IRE_evalVarSemElemT"
external evalTensor : weight -> weight -> weight = "IRE_evalTensor"
external getZeroTWt :  unit -> weight = "IRE_getZeroTWt"
external getOneTWt :  unit  -> weight = "IRE_getOneTWt"
external getZeroWt :  unit  -> weight = "IRE_getZeroWt"
external detensor : weight -> weight = "IRE_detensor"
external getOneWt :  unit  -> weight = "IRE_getOneWt"
external printWrappedWeight : weight -> int -> unit = "IRE_printWrappedWeight"


let mkOne () = One;;
let mkZero () = Zero;;

let globalStarCounter = ref 0;;

(*  ---- cache stuff for evaluation functions ---- *)

let debugEvalCacheLogging = ref false;;

let debugEvalCache s = if !debugEvalCacheLogging then (printf s; flush stdout) else ();;

let evalCache = Hashtbl.create 100000;;
let evalTCache = Hashtbl.create 100000;;

let clearEvalCaches () =
    debugEvalCache "cache CLEARED for both eval U and T\n";
    Hashtbl.clear evalCache;
    Hashtbl.clear evalTCache
;;

(*  ---- non-simplifying construction functions (for debugging only) ---- *)
(* ALSO CHANGE BACK THE LET REC BELOW *)
(*
let mkVar a = Var(a);;
let mkWeight a = Weight(a);;
let mkProject c = Project(c);;
let mkPlus a b = Plus(a, b);;
let mkDot a b = Dot(a, b);;
let mkDetensor a b = Detensor(a, b);;
let mkKleene a = Kleene(a);;
let mkVarT a = VarT(a);;
let mkProjectT c = ProjectT(c);;
let mkPlusT a b = PlusT(a, b);;
let mkDotT a b = DotT(a, b);;
let mkKleeneT a = KleeneT(a);;
let mkTensor a b = Tensor(a,b);;
*)
(* ---- regExp simplifying constructors ---- *)

let mkVar a =
    Var(a)
;;
let mkWeight a =
    Weight(a)
;;
let mkProject c =
  match c with
    | Zero -> Zero
    | One -> One
    | Weight(w) -> Weight (evalProjectSemElem w)
    | _ -> Project(c)
;;
let rec mkPlus a b =
(* let p = RegExpPair(a, b) in ( *)
  match a, b with
    |  Zero, d -> d
    |  c, Zero -> c
    |  Weight(w1), Weight(w2) -> Weight (evalPlusSemElem w1 w2)
    |  Plus(d,Weight(w1)),Weight(w2) -> mkPlus d (mkPlus (Weight w1) (Weight w2))
    |  Weight(w1),Plus(Weight(w2),c) -> mkPlus (mkPlus (Weight w1) (Weight w2)) c
    (* |  c, c -> c (*  Plus is idempotent *) (* Can we even do this in OCaml? *) *)
    |  c, d -> Plus(c,d)
;;
let rec mkDot a b =
(* let p = RegExpPair(a, b) in ( *)
  match a, b with
    |  Zero, _ -> Zero
    |  _, Zero -> Zero
    |  One, d -> d
    |  c, One -> c
    |  Weight(w1), Weight(w2) -> Weight (evalDotSemElem  w1 w2)
    |  Dot(d,Weight(w1)),Weight(w2) -> mkDot d (mkDot (Weight w1) (Weight w2))
    |  Weight(w1),Dot(Weight(w2),c) -> mkDot (mkDot (Weight w1) (Weight w2)) c
    |  c, d -> Dot(c, d)
;;
let rec mkKleene a =
  match a with
    | Zero -> One
    | One -> One
    | Weight w -> Weight(evalKleeneSemElem w 0)
    | Plus (One,b) -> mkKleene b
    | Plus (b,One) -> mkKleene b
    | Kleene (e,k) -> a (*  Kleene-star is idempotent: e** = e* *)
    | _ -> (incr globalStarCounter; Kleene(a,!globalStarCounter) )

;;
(*  regExpT simplifying constructors -------------------------- *)

let mkVarT a =
    VarT(a)
;;
let mkProjectT c =
  match c with
    | ZeroT -> ZeroT
    | OneT -> OneT
    | _ -> ProjectT c
;;
let mkPlusT a b =
(* let p = RegExpTPair(a, b) in ( *)
  match a, b with
    |  ZeroT, d -> d
    |  c, ZeroT -> c
    (*|  c, c -> c   *)
    |  c, d -> PlusT(c,d)
;;
let mkTensor a b =
(* let p = RegExpPair(a, b) in ( *)
  match a, b with
    |  Zero, d -> ZeroT
    |  c, Zero -> ZeroT
    |  One, One -> OneT
    |  c, d -> Tensor(c,d)
;;
let rec mkDotT a b =
(* let p = RegExpTPair(a, b) in ( *)
  match a, b with
    |  ZeroT, _ -> ZeroT
    |  _, ZeroT -> ZeroT
    |  OneT, d -> d
    |  c, OneT -> c
    |  Tensor(w,x), Tensor(y,z) ->
        mkTensor (mkDot y w) (mkDot x z)
    |  DotT(d,Tensor(w,x)),Tensor(y,z) ->
        mkDotT d (mkTensor (mkDot y w) (mkDot x z))
    |  Tensor(w,x),DotT(Tensor(y,z),c) ->
        mkDotT (mkTensor (mkDot y w) (mkDot x z)) c
    |  c, d -> DotT(c,d)
;;
let rec mkKleeneT a =
  match a with
    | ZeroT -> OneT
    | OneT -> OneT
    | PlusT (OneT,b) -> mkKleeneT b
    | PlusT (b,OneT) -> mkKleeneT b
    | KleeneT (e,k) -> a (*  Kleene-star is idempotent: e** = e* *)
    | _ -> (incr globalStarCounter; KleeneT(a,!globalStarCounter))
;;

(* mutually recursive simplifying constructors : *)

let rec mkDetensor a b =
(* let p = RegExpUTPair(a, b) in ( *)
  match a, b with
    |  Zero, _ -> Zero
    |  _, ZeroT -> Zero
    |  u, OneT -> u
    |  Weight(wu), Tensor(Weight(wl),Weight(wr)) ->
        let evalUChild = evalRegExp a and
            evalTChild = evalT b in
        let oneTensorU = evalTensor (getOneWt ()) evalUChild
        in Weight (detensor (evalDotSemElemT oneTensorU evalTChild))
(* RegExpUTPair(Weight(wu), Tensor(Weight(wl),rChild)): *)
(*   Detensor(One(), Tensor(mkDot(Weight(wl),a),rChild)), *)
(* RegExpUTPair(Weight(wu), Tensor(lChild,Weight(wr))): *)
(*   Detensor(One(), Tensor(lChild, mkDot(a,Weight(wr)))), *)
    |  u, t -> Detensor(u, t)


(*  ---- evaluation functions ---- *)

(*  Note: This version of eval does not take an assignment as a parameter; *)
(*    instead, it expects the client to provide an implementation of *)
(*    evalVarSemElem(v), which is expected to know how to retrieve values from *)
(*    the desired assignment, perhaps by looking up the variable number in a *)
(*    global assignment variable. *)


(* ALSO CHANGE THIS LET REC: *)
(*
let rec
*)
and evalRegExp e =
    (*try Hashtbl.find evalRegExpCache e *)
    try let w = Hashtbl.find evalCache e in (debugEvalCache "cache HIT  in eval U cache\n"; w)
    with Not_found -> (let w = evalRegExpCacheMiss e in
                       Hashtbl.add evalCache e w;
                       debugEvalCache "cache MISS in eval U cache\n";
                       w)

and evalRegExpCacheMiss e =
  match e with
    | Var v -> evalVarSemElem v
    | Zero -> getZeroWt ()
    | One -> getOneWt ()
    | Weight weight -> weight
    | Project(child) ->
      let evalChild = evalRegExp child
      in  evalProjectSemElem evalChild
    | Plus(lChild, rChild) ->
      let evalLChild = evalRegExp lChild and
          evalRChild = evalRegExp rChild
      in evalPlusSemElem evalLChild evalRChild
    | Dot(lChild, rChild) ->
      let evalLChild = evalRegExp lChild and
          evalRChild = evalRegExp rChild
      in evalDotSemElem evalLChild evalRChild
    | Kleene(child,starKey) ->
      let evalchild = evalRegExp child
      in evalKleeneSemElem evalchild starKey
    | Detensor(uChild,tChild) ->
(*  Note: We could have a callback for evalDetensor in the future. *)
(*  *)
(*  IDEA: return DetensorTranspose(DotT(Tensor(One(),u),t)) *)
(*  *)
      let evalUChild = evalRegExp uChild and
          evalTChild = evalT tChild in
      let oneTensorU = evalTensor (getOneWt ()) evalUChild
      in detensor (evalDotSemElemT oneTensorU evalTChild)

(*and detensor a =
    detensorTranspose(a)   *)

(*  Note: This version of eval does not take an assignment as a parameter; *)
(*    instead, it expects the client to provide an implementation of *)
(*    evalVarSemElemT(v), which is expected to know how to retrieve values from *)
(*    the desired assignment, perhaps by looking up the variable number v in a *)
(*    global assignment variable.  However, in the Newton-CRA usage of this *)
(*    function, there were no tensored variables, so evalVarSemElemT was never *)
(*    used.  However, this function does call evalRegExp, which has an analogous *)
(*    issue, and the analogous callback function evalVarSemElem(v) was used. *)

and evalT e =
    try let w = Hashtbl.find evalTCache e in (debugEvalCache "cache HIT  in eval T cache\n"; w)
    (*try Hashtbl.find evalTCache e  *)
    with Not_found -> (let w = evalTCacheMiss e in
                       Hashtbl.add evalTCache e w;
                       debugEvalCache "cache MISS in eval T cache\n";
                       w)

and evalTCacheMiss e =
  match e with
    | VarT v -> evalVarSemElemT v
(* placeholder, should never be evaluated due to our *)
(*   use case of evalT - there are no varT types *)
    | ZeroT -> getZeroTWt ()
    | OneT -> getOneTWt ()
    | ProjectT(child) ->
      let c = evalT child
      in evalProjectSemElemT c
    | PlusT(lChild,rChild) ->
      let lVal = evalT lChild and
          rVal = evalT rChild
      in evalPlusSemElemT lVal rVal
    | DotT(lChild,rChild) ->
      let lVal = evalT lChild and
          rVal = evalT rChild
      in evalDotSemElemT lVal rVal
    | KleeneT(child,starKey) ->
      let cVal = evalT child
      in  evalKleeneSemElemT cVal starKey
    | Tensor(lChild, rChild) ->
      let lVal = evalRegExp lChild and
          rVal = evalRegExp rChild
      in  evalTensor lVal rVal
;;
(*  ---- core functions of ICRA regular expression transformation ---- *)

(*  Substitute s for free occurrences of x in e, where "free" occurrences are *)
(*    defined to be those that do not occur under a star. *)
(*  NOTE: In the Newton-CRA project, we could have avoided calling into *)
(*    substFreeT in the Detensor case because we knew that the expression *)
(*    e is "normal" in the terminology of the POPL 2017 submission, i.e., that *)
(*    the right child of every Detensor subexpression of e is a KleeneT. *)
let rec substFree s x e =
  match e with
    | Var v -> if (v = x) then s else e
    | Zero -> e
    | One -> e
    | Weight weight -> e
    | Project (child) -> mkProject (substFree s x child)
    | Plus (lChild, rChild) -> mkPlus (substFree s x lChild) (substFree s x rChild)
    | Dot (lChild, rChild) -> mkDot (substFree s x lChild) (substFree s x rChild)
    | Kleene (child, starKey) -> e
    | Detensor (uChild,tChild) ->
            mkDetensor (substFree s x uChild) (substFreeT s x tChild)
(* Detensor(uChild,tChild): *)
(*   mkDetensor(substFree(s,x,uChild),tChild)   assume e is normal *)

(*  Substitute s for free occurrences of the variable x in e, where x is *)
(*    interpreted as the number of some untensored variable, i.e., we will not *)
(*    substitute for occurrences of the tensored variable with number x. *)
and substFreeT s x e =
  match e with
    | VarT v -> e
    | ZeroT -> e
    | OneT -> e
    | ProjectT child -> mkProjectT (substFreeT s x child)
    | PlusT(lChild, rChild) -> mkPlusT (substFreeT s x lChild) (substFreeT s x rChild)
    | DotT(lChild, rChild) -> mkDotT (substFreeT s x lChild) (substFreeT s x rChild)
    | KleeneT(child, starKey) -> e
    | Tensor(lChild, rChild) -> mkTensor (substFree s x lChild) (substFree s x rChild)
;;

let rec factorAux x e =
  match e with
    | Var v -> if (v = x) then (Zero, OneT) else (e, ZeroT)
    | Zero -> (Zero, ZeroT)
    | One -> (One, ZeroT)
    | Weight weight -> (e, ZeroT)
    | Project child ->
      let u, t = (factorAux x child) in
      (*match childPair with
        |  u,t -> *)
      (mkProject u, mkProjectT t)
    | Plus (lChild, rChild) ->
      let lu,lt = (factorAux x lChild) and
          ru,rt = (factorAux x rChild) in
  (*match lChildPair with
    |  lu,lt ->
  match rChildPair with
    |  ru,rt -> *)
              ((mkPlus lu ru), (mkPlusT lt rt))
    | Dot (lChild, rChild) ->
      let lu,lt = (factorAux x lChild) and
          ru,rt = (factorAux x rChild) in
    (*  let lChildPair = factorAux(x, lChild)  and
          rChildPair = factorAux(x, rChild)  *)
  (*match lChildPair with
    |  lu,lt ->
  match rChildPair with
    |  ru,rt -> *)
              (
                (mkDot lu ru)
                ,
                (mkPlusT
                  (mkDotT lt (mkTensor One ru))
                  (mkDotT rt (mkTensor lChild One))
                )
              )
    | Kleene (child,starKey) -> (e, ZeroT)
    | Detensor (uChild,tChild) ->
      let uu,ut = (factorAux x uChild)
  (*match uChildPair with
    |  uu,ut ->  *)
      in  ((mkDetensor uu tChild),
           (mkDotT ut tChild));;

(*  Given a variable x and a regular expression e, *)
(*   produce a new expression ( u \detensorproduct t* ) *)
let isolate x e =
  let u,t = factorAux x e in
  (* match p with
    |  u,t -> *)
  mkDetensor u (mkKleeneT t);;

(*  ---- general substitution functions, not currently used ---- *)

(*  Substitute s for x in e *)
let rec subst s x e =
  match e with
    | Var v -> if (x == v) then s else e
    | Zero -> e
    | One -> e
    | Weight weight -> e
    | Project (child) -> mkProject (subst s x child)
    | Plus (lChild, rChild) -> mkPlus (subst s x lChild) (subst s x rChild)
    | Dot (lChild, rChild) -> mkDot (subst s x lChild) (subst s x rChild)
    | Kleene (child, starKey) -> mkKleene (subst s x child)
    | Detensor (uChild,tChild) -> mkDetensor (subst s x uChild) (substT s x tChild)

(*  Substitute s for the variable x in e, where x is interpreted as the number *)
(*    of some untensored variable, so, we will not substitute for occurrences of *)
(*    the tensored variable with numbre x. *)
and substT s x e =
  match e with
    | VarT v -> e
    | ZeroT -> e
    | OneT -> e
    | ProjectT (child) -> mkProjectT (substT s x child)
    | PlusT (lChild, rChild) -> mkPlusT (substT s x lChild) (substT s x rChild)
    | DotT (lChild, rChild) -> mkDotT (substT s x lChild) (substT s x rChild)
    | KleeneT (child, starKey) -> mkKleeneT (substT s x child)
    | Tensor (lChild,rChild) -> mkTensor (subst s x lChild) (subst s x rChild)
;;

(*  ---- printing functions ---- *)

let rec indent i =
    if (i <= 0) then ()
    else (print_char ' '; print_char ' '; indent (i - 1))

let rec printRegExpAux e i =
    match e with
    | Zero -> indent i; (printf "Zero()\n")
    | One -> indent i; (printf "One()\n")
    | Var(v) -> indent i; (printf "Var(%d)\n" v)
    | Weight(w) -> indent i; (printf "Weight(");
                   flush stdout;
                   (printWrappedWeight w (i+1));
                   indent i; (printf ")\n")
    | Project(c) -> indent i; (printf "Project(\n");
                    printRegExpAux c (i+1);
                    indent i; (printf ")\n")
    | Plus(c1,c2) -> indent i; (printf "Plus(\n");
                     printRegExpAux c1 (i+1);
                     indent (i+1); (printf ",\n");
                     printRegExpAux c2 (i+1);
                     indent i; (printf ")\n")
    | Dot(c1,c2) ->  indent i; (printf "Dot(\n");
                     printRegExpAux c1 (i+1);
                     indent (i+1); (printf ",\n");
                     printRegExpAux c2 (i+1);
                     indent i; (printf ")\n")
    | Kleene(c,k) -> indent i; (printf "Kleene( key=%d\n" k);
                     printRegExpAux c (i+1);
                     indent i; (printf ")\n")
    | Detensor(cu,ct) -> indent i; (printf "Detensor(\n");
                         printRegExpAux cu (i+1);
                         indent (i+1); (printf ",\n");
                         printRegExpTAux ct (i+1);
                         indent i; (printf ")\n")

and printRegExpTAux e i =
    match e with
    | ZeroT -> indent i; (printf "Zero()\n")
    | OneT -> indent i; (printf "One()\n")
    | VarT(v) -> indent i; (printf "VarT(%d)\n" v)
 (*   | WeightT(w) -> indent i; (printf "WeightT(??)\n") *)
    | ProjectT(c) -> indent i; (printf "ProjectT(\n");
                     printRegExpTAux c (i+1);
                     indent i; (printf ")\n")
    | PlusT(c1,c2) -> indent i; (printf "PlusT(\n");
                      printRegExpTAux c1 (i+1);
                      indent (i+1); (printf ",\n");
                      printRegExpTAux c2 (i+1);
                      indent i; (printf ")\n")
    | DotT(c1,c2) -> indent i; (printf "DotT(\n");
                     printRegExpTAux c1 (i+1);
                     indent (i+1); (printf ",\n");
                     printRegExpTAux c2 (i+1);
                     indent i; (printf ")\n")
    | KleeneT(c,k) -> indent i; (printf "KleeneT( key=%d\n" k);
                      printRegExpTAux c (i+1);
                      indent i; (printf ")\n")
    | Tensor(c1,c2) -> indent i; (printf "Tensor(\n");
                       printRegExpAux c1 (i+1);
                       indent (i+1); (printf ",\n");
                       printRegExpAux c2 (i+1);
                       indent i; (printf ")\n")

let printRegExp e = printRegExpAux e 0; flush stdout;;
let printRegExpT e = printRegExpTAux e 0; flush stdout;;

(*  ---- introspection functions ---- *)

let getLChild e =
  match e with
    | Project l -> l
    | Plus (l,r) -> l
    | Dot (l,r) -> l
    | Kleene(l,k) -> l
    | _ -> Zero;;

let getRChild e =
  match e with
    | Plus (l,r) -> r
    | Dot (l,r) -> r
    | _ -> Zero;;

let getLChildT e =
  match e with
    | PlusT (l,r) -> l
    | DotT (l,r) -> l
    | KleeneT (l,k) -> l
    | ProjectT (l) -> l
    | _ -> ZeroT;;

let getRChildT e =
  match e with
    | PlusT (l,r) -> r
    | DotT (l,r) -> r
    | _ -> ZeroT;;



let isZero e =
  match e with
    | Zero -> true
    | _ -> false;;

let isOne e =
  match e with
    | One -> true
    | _ -> false;;

let isVar e =
  match e with
    | Var v -> true
    | _ -> false;;

let isWeight e =
  match e with
    | Weight w -> true
    | _ -> false;;

let isProject e =
  match e with
    | Project _ -> true
    | _ -> false;;

let isPlus e =
  match e with
    | Plus (_,_) -> true
    | _ -> false;;

let isDot e =
  match e with
    | Dot (_,_) -> true
    | _ -> false;;

let isKleene e =
  match e with
    | Kleene (_,_) -> true
    | _ -> false;;

let isZeroT e =
  match e with
    | ZeroT -> true
    | _ -> false;;

let isOneT e =
  match e with
    | OneT -> true
    | _ -> false;;

let isVarT e =
  match e with
    | VarT v -> true
    | _ -> false;;

let isProjectT e =
  match e with
    | ProjectT (_) -> true
    | _ -> false;;

let isPlusT e =
  match e with
    | PlusT (_,_) -> true
    | _ -> false;;

let isDotT e =
  match e with
    | DotT (_,_) -> true
    | _ -> false;;

let isKleeneT e =
  match e with
    | KleeneT (_,_) -> true
    | _ -> false;;

let isTensor e =
  match e with
    | Tensor (_,_) -> true
    | _ -> false;;

(*  ---- exported function callbacks ---- *)
(* These functions are defined in OCaml may be called externally (e.g., from C) *)

let _ = (*  Jason manually added this line... *)
(*  Printing operations *)
  Callback.register "IRE_printRegExp" printRegExp;
  Callback.register "IRE_pringRegExpT" printRegExpT;
(*  Nullary construction operations *)
  Callback.register "IRE_mkZero" mkZero;
  Callback.register "IRE_mkOne" mkOne;
(*  Unary construction operations *)
  Callback.register "IRE_mkKleene" mkKleene;
  Callback.register "IRE_mkKleeneT" mkKleeneT;
  Callback.register "IRE_mkVar" mkVar;
  Callback.register "IRE_mkVarT" mkVarT;
  Callback.register "IRE_mkWeight" mkWeight;
  Callback.register "IRE_mkProject" mkProject;
  Callback.register "IRE_mkProjectT" mkProjectT;

(*  Binary construction operations *)
  Callback.register "IRE_mkPlus" mkPlus;
  Callback.register "IRE_mkDot" mkDot;
  Callback.register "IRE_mkPlusT" mkPlusT;
  Callback.register "IRE_mkDotT" mkDotT;
  Callback.register "IRE_mkTensor" mkTensor;

(*  Miscellaneous operations *)
  Callback.register "IRE_evalT" evalT;
  Callback.register "IRE_evalRegExp" evalRegExp;
  Callback.register "IRE_detensor" detensor;

(*
  (* These are no longer used *)
  Callback.register "IRE_updateAssignmentList" updateAssignmentList;
  Callback.register "IRE_initAssignmentList" initAssignmentList;
  Callback.register "IRE_checkEqual" checkEqual;
  Callback.register "IRE_getVarNum" getVarNum;
  Callback.register "IRE_getDVarNum" getDVarNum;
  Callback.register "IRE_getNumPairs" getNumPairs;
  Callback.register "IRE_getPairL" getPairL;
  Callback.register "IRE_getPairR" getPairR;
  Callback.register "IRE_getTListLength" getTListLength;
  Callback.register "IRE_getDListLength" getDListLength;
  Callback.register "IRE_getTFromRegList" getTFromRegList;
  Callback.register "IRE_getPFromRegList" getPFromRegList;
  Callback.register "IRE_getAssignment" getAssignment;
  Callback.register "IRE_getNextPList" getNextPList;
  Callback.register "IRE_isNullTList" isNullTList;
  Callback.register "IRE_getNextTList" getNextTList;
  Callback.register "IRE_getRegExpTFromTList" getRegExpTFromTList;
  Callback.register "IRE_mapDotOnRight" mapDotOnRight;
  Callback.register "IRE_mapDotOnLeft" mapDotOnLeft;
  Callback.register "IRE_mapDotBothSides" mapDotBothSides;
  Callback.register "IRE_mapDotTOnRight" mapDotTOnRight;
  Callback.register "IRE_mapPlusT" mapPlusT;
  Callback.register "IRE_mapPlus" mapPlus;
*)
  Callback.register "IRE_isOne" isOne;
  Callback.register "IRE_isZero" isZero;
  Callback.register "IRE_isVar" isVar;
  Callback.register "IRE_isWeight" isWeight;
  Callback.register "IRE_isProject" isProject;
  Callback.register "IRE_isKleene" isKleene;
  Callback.register "IRE_isPlus" isPlus;
  Callback.register "IRE_isDot" isDot;
  Callback.register "IRE_isOneT" isOneT;
  Callback.register "IRE_isZeroT" isZeroT;
  Callback.register "IRE_isVarT" isVarT;
  Callback.register "IRE_isProjectT" isProjectT;
  Callback.register "IRE_isKleeneT" isKleeneT;
  Callback.register "IRE_isPlusT" isPlusT;
  Callback.register "IRE_isDotT" isDotT;
  Callback.register "IRE_isTensor" isTensor;
  Callback.register "IRE_getLChild" getLChild;
  Callback.register "IRE_getRChild" getRChild;
  Callback.register "IRE_getLChildT" getLChildT;
  Callback.register "IRE_getRChildT" getRChildT;
  Callback.register "IRE_isolate" isolate;
  Callback.register "IRE_substFree" substFree;;
  Callback.register "IRE_clearEvalCaches" clearEvalCaches;;
(*  Jason manually added this line *)
(* the end *)
