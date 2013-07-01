header {* Refinement Calculus for OO *}

(*<*) theory rcos imports Main graph_utl begin (*>*)

types 
  'a pred = "'a => bool"
  'a predT = "'a pred => 'a pred"

constdefs
"true == %u. True"
"false == %u. False"
"imp p q == % u. (p u) --> (q u)"
"andd p q == (%u. ((p u) & (q u)))"
"or p q == (%u. ((p u) | (q u)))"
"not p == (%u. (~ (p u)))" (* changed a bit *)


constdefs
"glb P == (%u. (ALL p. (P p --> p u)))"
"lub P == (%u. (EX p. (P p & p u)))"
"implies p q == ALL u. (p u) --> (q u)"
"fix f == glb (%p. (implies (f p) p))"
eq_pred (infixl "eq" 30) where "p eq q == (implies p q) & (implies q p)"

constdefs
"skip q == q"
"abort q == false"
"magic q  == true"
"assert g q == andd g q"
"guard b q == imp b q"
"nondass P l q == (%v. (wfGraph v) & (wfPathl l v) & (ALL v1. P v v1 --> q v1))"
"Dch F q == glb (%p. EX c. F c & (p = c q))"
"Ach F q == lub (%p. EX c. F c & (p = c q))"
"cond g c1 c2 q == or (andd g (c1 q))  (andd (not g) (c2 q))"
 "do g c q == fix (%p. (or (andd (not g) q) (andd g (c p))))"
"block p c q == (%u. ALL x. p(x,u) --> c (%v. q (snd v)) (x,u))"
seq (infixr ";" 60) where "(c1; c2) q == c1 (c2 q)"
"pp p r l == assert p ; nondass r l"
"update P q == %v. q (P v)"

constdefs 
(* "assign e p q == %u. wfGraph u & wfPath p u & q (e u)"  *)
"assign p e q == %u. wfGraph u & wfPath p u & wfExp e u & q (swingPath p (getNodeExp e u) u)"
(* f: mapping from local variables to their initial values *)
"begin f q == %u. wfGraph u & wflabelExpF f u & q (Vars f u)"
"end q == %u. wfGraph u & q (removeSnode u)" 
(* Cannot use "local" as name here; it is Isabelle keyword. *)
(* "locdec f c  == %u. ((begin f; c; end) q) u" *)
"locdec f c == begin f; c; end"
(*Method call defined using local variables. c: method body followed by the assignment from return parameter to argument *)
"method l c == locdec (getLabelExpF l) c"
"object l s q == %u. wfGraph u & wfPath l u & wflabelExpF (getAttrsOfCtype s) u & q (addObject l s u)"

constdefs
"monotonic c == (ALL p q. (implies p q) --> (implies (c p) (c q)))"
"conjunctive c == (ALL P. c (glb P) = glb (%q. EX p. P p & (q = c p)))"
refines (infixl "ref" 40) where "c1 ref c2 == ALL q. (implies (c1 q) (c2 q))"
eq_design (infixl "eq" 30) where "c1 eq c2 == (c1 ref c2) & (c2 ref c1)"
"mu f == Dch (%c. monotonic c & (refines c (f c)))"
"lift c q u == c (%v. q (fst u, v)) (snd u)"
(* "adapt f g c == (assign f); (lift c) ; (assign g)" *)
(* "call c f g v == block (%x. fst x = v (snd x)) (adapt f g c)" *)
"par c1 c2 q == %(s1,s2). (EX q1 q2. (ALL s1p s2p. q1 s1p & q2 s2p --> q (s1p,s2p)) & 
  c1 q1 s1 & c2 q2 s2)"


(* Lemmas *)

lemma "do g c ref (do g (assert g; c))"
apply (simp add:refines_def implies_def do_def fix_def not_def andd_def or_def glb_def assert_def seq_def)
done


lemma glb_is_lower : "P p ==> implies (glb P) p"
by (simp add:glb_def implies_def, auto)

lemma glb_is_the_lowest : "(!!x. P x ==> implies p x) ==> implies p (glb P)"
by(simp add:glb_def implies_def, auto) 

definition "MyP f = (%p. (implies (f p) p))"

lemma fact1 : "monotonic f ==> MyP f p ==> MyP f (f p)"
by (simp add:monotonic_def MyP_def)

lemma fact3 : "!!x. MyP f x ==> implies (glb (MyP f)) x"
by (simp add:glb_def implies_def, auto)

lemma fact4 : "(!!x. MyP f x ==> implies p x) ==> implies p (glb (MyP f)) "
by (cut_tac P = "MyP f" and p="p" in glb_is_the_lowest)

theorem implies_transitive :"implies x y ==> implies y z ==> implies x z"
by (simp add:implies_def)

lemma fact6 : "MyP f x ==> implies q (f x) ==> implies q x"
apply (simp add:MyP_def)
apply (insert implies_transitive [of q "(f x)" x], auto)
done

lemma fix1 : "monotonic f ==> implies (f (fix f))  (fix f)"
apply (simp add:fix_def)
apply (subgoal_tac "monotonic f ==> implies (f (glb (MyP f))) (glb (MyP f))")
apply (simp add:MyP_def)
apply (simp add:monotonic_def fact3 fact6 fact4)
done

lemma fix2 : "monotonic f ==> implies  (fix f) (f (fix f)) "
apply (subgoal_tac "monotonic f ==> MyP f (fix f)")
prefer 2
apply (subgoal_tac "monotonic f ==> implies (f (glb (MyP f))) (glb (MyP f))")
prefer 2
apply (simp add:monotonic_def fact3 fact6 fact4)
apply (simp add:fix_def MyP_def)
apply (cut_tac f="f" and p = "fix f" in fact1) 
apply(assumption)+
apply (cut_tac P = "MyP f" and p = "f (fix f)" in glb_is_lower) 
apply (assumption)
apply (simp add:fix_def MyP_def)
done

(* Tarski *)
theorem fix_is_fixpoint : "monotonic f ==> (fix f) eq (f (fix f))"
by(simp add:eq_pred_def fix1 fix2)


(*****)

lemma fact22 : "(!!p. (Q p --> P p)) ==> implies (glb P) (glb Q)"
apply(subgoal_tac "!!p. P p ==> implies (glb P) p")
prefer 2 apply (simp add:glb_is_lower)
apply (subgoal_tac "!!p. Q p ==> implies (glb P) p")
prefer 2 apply simp
apply (cut_tac P="Q" and p="glb P" in glb_is_the_lowest, auto)
done

lemma fact21 : "c ref d ==> implies (fix c) (fix d)"
apply (simp add:refines_def fix_def)
apply (cut_tac P ="(%p. implies (c p) p)" and Q = "(%p. implies (d p) p)" in fact22, auto)
apply (subgoal_tac "implies (c p) (d p)")
apply (cut_tac x="(c p)" and y = "(d p)" and z= "p" in implies_transitive, auto)
done

theorem do_ref : "c ref d ==> (do g c) ref (do g d)"
apply (simp add:refines_def do_def, auto)
apply (subgoal_tac "(%p. or (andd (not g) q) (andd g (c p))) ref (%p. or (andd (not g) q) (andd g (d p)))")
apply (cut_tac c = "(%p. or (andd (not g) q) (andd g (c p)))" and d = "(%p. or (andd (not g) q) (andd g (d p)))" in fact21, auto)
apply (simp add: refines_def implies_def fix_def glb_def andd_def or_def not_def)
done

theorem seq_ref_right : "monotonic e ==> c ref d ==>  (e ; c) ref (e ; d)"
by (simp add:monotonic_def refines_def  seq_def)

theorem seq_ref_left : "c ref d ==>  (c ; e) ref (d ; e)"
by (simp add:refines_def  seq_def)

theorem ref_reflexive : "x ref x"
apply (simp add:refines_def implies_def)
done

theorem ref_transitive : "x ref y ==> y ref z ==> x ref z"
apply (simp add:refines_def, auto)
apply (rename_tac r)
apply (subgoal_tac "implies (x r) (y r)")
apply (subgoal_tac "implies (y r) (z r)")
apply (cut_tac x = "(x r)" and y = "(y r)" and z = "(z r)" in implies_transitive, auto)
done

theorem seq_ref : "monotonic c ==> c ref d ==> e ref f ==> (c ; e) ref (d ; f)"
apply (subgoal_tac "(c ; e) ref (c ; f)")
apply (subgoal_tac "(c ; f) ref (d ; f)")
apply (cut_tac x = "(c ; e)" and y = "(c ; f)" and z = "(d ; f)" in ref_transitive)
apply (simp add:seq_ref_right seq_ref_left)+
done

theorem pp_monotonic : "monotonic (pp p r l)"
apply (simp add:monotonic_def pp_def seq_def nondass_def true_def assert_def andd_def implies_def) 
done

theorem assign_monotonic: "monotonic (assign p e)"
apply (simp add:monotonic_def assign_def implies_def, auto)
apply (subgoal_tac "pa (fst (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)), 
                        fst (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b))),
                        fst (snd (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)))), 
                        snd (snd (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)))))")
apply (subgoal_tac "q (fst (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)), 
                        fst (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b))),
                        fst (snd (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)))), 
                        snd (snd (snd (swingPath p (getNodeExp e (a, aa, ab, b)) (a, aa, ab, b)))))")
apply simp  
apply (drule spec mp)+
apply assumption
apply simp+
done

theorem cond_ref: "c ref d & e ref f ==> (cond g c e) ref (cond g d f)"
apply (simp add:refines_def cond_def andd_def or_def implies_def)
done

theorem begin_monotonic: "monotonic (begin l)"
apply (simp add:monotonic_def begin_def implies_def, auto)
(*Should look for a better way to prove: "ALL a aa ab b. p (, , , ,) --> q (, , , ,); p g ==> q g"*)
apply (subgoal_tac " p (fst (Vars l (a, aa, ab, b)), fst (snd (Vars l (a, aa, ab, b))),
                        fst (snd (snd (Vars l (a, aa, ab, b)))), snd (snd (snd (Vars l (a, aa, ab, b)))))")
apply (subgoal_tac " q (fst (Vars l (a, aa, ab, b)), fst (snd (Vars l (a, aa, ab, b))),
                        fst (snd (snd (Vars l (a, aa, ab, b)))), snd (snd (snd (Vars l (a, aa, ab, b)))))")
apply (simp)
(*Apply multiple times of drule spec because of ALL a aa ab b, strictly, four times*)
apply (drule spec)+
apply (drule mp)
apply assumption+
apply auto
done

theorem end_monotonic: "monotonic (end)"
apply (simp add:monotonic_def end_def implies_def, auto)
apply (subgoal_tac " p (fst (removeSnode (a, aa, ab, b)), fst (snd (removeSnode (a, aa, ab, b))),
                        fst (snd (snd (removeSnode (a, aa, ab, b)))), snd (snd (snd (removeSnode (a, aa, ab, b)))))")
apply (subgoal_tac " q (fst (removeSnode (a, aa, ab, b)), fst (snd (removeSnode (a, aa, ab, b))),
                        fst (snd (snd (removeSnode (a, aa, ab, b)))), snd (snd (snd (removeSnode (a, aa, ab, b)))))")
apply (simp)
apply (drule spec)+
apply (drule mp)
apply assumption+
apply auto
done

lemma seq_associative: "(c; d; e) p = ((c; d); e) p"
apply (simp add:seq_def)
done

theorem seq_monotonic: "monotonic c ==> monotonic d ==> monotonic (c ; d)" 
apply (simp add:monotonic_def, auto)
apply (subgoal_tac "implies (d p) (d q)")
prefer 2
apply simp
apply (subgoal_tac "implies (c (d p)) (c (d q))")
prefer 2
apply simp
apply (simp add:seq_def)
done

theorem cond_monotonic: "monotonic c ==> monotonic d ==> monotonic (cond g c d)" 
apply (simp add:monotonic_def, auto)
apply (subgoal_tac "implies (d p) (d q)")
prefer 2
apply simp
apply (subgoal_tac "implies (c p) (c q)")
prefer 2
apply simp
apply (simp add:cond_def andd_def or_def implies_def)
done

theorem do_monotonic: "monotonic c ==> monotonic (do g c)" 
apply (simp add:monotonic_def, auto)
apply (subgoal_tac "implies (c p) (c q)")
prefer 2
apply simp
apply (simp add:do_def)
apply (cut_tac c = "%pa. or (andd (not g) p) (andd g (c pa))" 
           and d = "%p. or (andd (not g) q) (andd g (c p))" in fact21, auto)
apply (simp add:refines_def implies_def andd_def or_def)
done

theorem method_monotonic: "monotonic c ==> monotonic (method l c)"
apply (simp add:monotonic_def method_def locdec_def, auto)
apply (cut_tac c = "begin (getLabelExpF l)" and d = "c" in seq_monotonic)
apply (cut_tac l = "(getLabelExpF l)" in begin_monotonic, auto)
apply (simp add:monotonic_def)
apply (cut_tac c = "begin (getLabelExpF l); c" and d = "end" in seq_monotonic, auto)
apply (insert end_monotonic, simp)
apply (simp add:monotonic_def)
apply (drule spec)+
apply (drule mp, assumption)
apply auto
apply (simp add:implies_def seq_def)
done

end