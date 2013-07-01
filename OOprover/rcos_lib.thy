header {* Library for Useful Lemmas for rCOS Refinement*}

theory rcos_lib imports rcos begin

lemma pp_strengthen_post : 
  " implies q2 q1 ==> 
  ((pp pre (%g. q1) p) ref (pp pre (%g. q2)) p)"
  by (simp add:refines_def pp_def assert_def seq_def nondass_def andd_def implies_def)

(*|- For any path p and any integer n, [ true|- p=n ] ref p:=n  *)
lemma ref_pp_assign : 
"pp (true) 
  (% g. % g1.((getIntOfPath p g1) = n)) [p]
  ref 
  (assign p (Val (Zint n)))"
proof -
  have f1: "!!q g.
    [| (ALL h. (getIntOfPath p h = n) --> q h); wfGraph g; wfPath p g |]
    ==> q (swingPath p (getNodeExp (Val (val.Zint n)) g) g)"
  proof -
    fix q g
    let ?h = "swingPath p (getNodeVal (Zint n)) g"
    assume h1 : "ALL h. getIntOfPath p h = n --> q h"
    assume h2 : "wfGraph g" 
    assume h3 : "wfPath p g"
    show "q (swingPath p (getNodeExp (Val (val.Zint n)) g) g)"
    proof - 
      from h1 have f1 : "getIntOfPath p ?h = n --> q ?h" ..
      from h2 h3 have f2 : "getIntOfPath p ?h = n"
	by (simp add:wfPathl_def sPCV_Int [of g p "n"])
      from f1 f2 have f3 : "q ?h" ..
      with f3 show "q (swingPath p (getNodeExp (Val (val.Zint n)) g) g)" 
                  by (simp add:getNodeExp_def)
    qed
  qed
  with f1 show ?thesis by (simp add:refines_def implies_def assign_def pp_def seq_def 
    assert_def true_def andd_def nondass_def wfPathl_def wfExp_def, auto)
qed

(* Expression Substitution *)

definition pe :: "path => path => exp => exp" where
"pe q p e == (if (p = q) then e else 
                         (case e of  (Path p1) => (case q of (r # p) => Path (r # p1) 
                                                            | _ => e)
                                 | _ => e) )" 

primrec subst :: "exp => path => exp => exp" where
"subst (Path q) p f = pe q p f"|
"subst (Val v) p f = Val v"|
"subst (undefExp) p f = undefExp"|
"subst (Plus e1 e2) p f = Plus (subst e1 p f) (subst e2 p f)"|
"subst (Minus e1 e2) p f = Minus (subst e1 p f) (subst e2 p f)"|
"subst (Times e1 e2) p f = Times (subst e1 p f) (subst e2 p f)"|
"subst (Divide e1 e2) p f = Divide (subst e1 p f) (subst e2 p f)"

lemma "wfGraph g ==> wfPath q g ==> pe q p e = Path r ==> pathInGraph q (swingPath p (getNodeExp e g) g)
       ==> pathInGraph r (swingPath p (getNodeExp e g) g)"
apply (simp add:pe_def)
apply (split split_if_asm, auto)
apply (cut_tac p = "q" and n = "(getNodeExp (Path r) g)" and g = "g" in swingPathChangeVertex, auto)
apply (simp add:pathInGraph_def swingPath_def)
apply (split split_if_asm, auto)
sorry

lemma "assign p e ; assign q f
       ref 
       assign p e ; assign q (subst f p e)"
apply (simp add:refines_def seq_def assign_def implies_def andd_def wfExp_def, auto)
apply (case_tac "subst f p e", auto)
apply (case_tac "f", auto)
sorry

(* For any path p and any integers m and n, |-(p := m) ref (p := n; p := p + (m -n)) *)
lemma assign_end : 
  "(assign p (Val (Zint m)))
  ref 
  (assign p (Val (Zint n)); 
  (assign p (Plus (Path p) (Val (Zint ((m::int) - n))))))"
apply (simp add:refines_def seq_def assign_def implies_def andd_def getNodeExp_def wfExp_def, auto)
apply (cut_tac p = "p" and n = "getNodeVal (Zint n)" and g = "(a, aa, ab, b)" in wfswingPath, auto)
apply (simp add:getNodeVal_def)
apply (cut_tac p = "p" and n = "n" and g = "(a, aa, ab, b)" in swingPathIntPreserveswfPath, auto)
apply (simp add:isIntPath_def)
apply (cut_tac p = "p" and n = "getNodeVal (Zint n)" and g = "(a, aa, ab, b)" in swingPathChangeVertex, auto)
apply (simp add:getNodeVal_def)+
apply (cut_tac g = "swingPath p (L (getVnodeFromVal (Zint n))) (a, aa, ab, b)" 
           and n = "Zint n" in getVnodeFromVal_spec, auto)
apply (simp add:isIntVal_def)+
apply (subgoal_tac "getIntOfPath p (swingPath p (getNodeVal (Zint n)) (a, aa, ab, b)) = n", auto)
apply (cut_tac p = "p" and m = "getNodeVal (Zint m)" and n = "getNodeVal (Zint n)" 
           and g = "(a, aa, ab, b)" in swingPathTransitive, auto)
apply (simp add:getNodeVal_def)+
apply (simp add:getIntOfPath_def getInt_def)
apply (cut_tac p = "p" and n = "getNodeVal (Zint n)" and g = "(a, aa, ab, b)" in swingPathChangeVertex, auto)
apply (simp add:getNodeVal_def)+
apply (cut_tac g = "swingPath p (L (getVnodeFromVal (Zint n))) (a, aa, ab, b)" 
           and n = "Zint n" in getVnodeFromVal_spec, auto)
done


(*************************************** Expert Pattern Example Refinement***************************)

(* Theorem: "EPIsRefOne"*)
(* p is a path of arbitrary length, with the form p = r1...rk; and m, n are integers.*)
(* class B {int x; m () {this.x := n}} *)
(* contract IP of I {A a; bar() {p.x := n}} *)
(* class C {A a; bar() {p.m()}} *)
(* |- I.bar() ref C.bar() *)


lemma getLEF:  "getLabelExpF  [(b, Path p)] = (%l. if l = b then Path p
                                                   else undefExp)"
apply (simp add:expand_fun_eq)
done

lemma wfforLabelExpF: "p ~=[] ==> wfGraph g ==> wfPath (a # p) g ==>
                       wflabelExpF (%l. if l = b then Path p
                                      else undefExp) g"
apply (simp add:wflabelExpF_def)
apply (simp add:wfExp_def)
apply (cut_tac g = "g" and p = "p" and a = "a" in wfforPathInGraph, auto)
done

theorem EPIsRefOne : "p~=[] -->
                      (assign (a # p) (Val (Zint n)) ref
                      (method [(b, Path p)] (assign (a # [b]) (Val (Zint n)))))"
apply (cut_tac b = "b" and p = "p" in getLEF)
apply (simp add:refines_def implies_def method_def locdec_def assign_def seq_def end_def seq_def begin_def)
apply (rule impI)
apply (rule allI)+
apply (rule impI)
apply (cut_tac g = "(aa, aaa, ab, ba)"  and p = "p" and a = "a"
           and b = "b" in wfforLabelExpF, auto)
apply (cut_tac g = "(aa, aaa, ab, ba)" and l = "getLabelExpF [(b, Path p)]" 
                 in wfVars, auto)
apply (cut_tac g = "(aa, aaa, ab, ba)"  and p = "p" and f = "getLabelExpF [(b, Path p)]" 
           and l = "b" and a = "a"  in wfPathforVars, auto)
apply (simp add:wfExp_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and 
       n = "getNodeExp (Val (val.Zint n)) (Vars (\<lambda>l. if l = b then Path p else undefExp) (aa, aaa, ab, ba))"
   and p = "p" and f = "getLabelExpF [(b, Path p)]" and l = "b" and a = "a" in wfforSwingPathVars, auto)
apply (simp add:getNodeExp_def getNodeVal_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and 
               m = "getNodeExp (Val (val.Zint n)) (aa, aaa, ab, ba)" and p = "p"
           and f = "getLabelExpF [(b, Path p)]" and l = "b" and a = "a" in sameGraphs, auto)
apply (simp add:getNodeExp_def getNodeVal_def)
apply (simp add:getNodeExp_def)
done


(*First theorem: "EPIsRefTwo"*)
(* p is a path of arbitrary length, with the form p = r1...rk; v is an arbitrary name *)
(* class B {int x; m (int v) {this.x := v}} *)
(* contract IP of I {A a; bar() {p.x := n}} *)
(* class C {A a; bar() {p.m(n)}} *)
(* |- I.bar() ref C.bar() *)


lemma getLEFT:  "getLabelExpF  [(b, Path p), (c, Val (Zint n))]
                = (%l. if l = b then Path p
                                else if l = c then Val (Zint n)
                                else undefExp)"
apply (simp add:expand_fun_eq)
done

lemma wfforLabelExpFT: "p ~=[] ==> wfGraph g ==> wfPath (a # p) g ==>
                       wflabelExpF (%l. if l = b then Path p
                                     else if l = c then Val (Zint n)
                                     else undefExp) g"
apply (simp add:wflabelExpF_def)
apply (simp add:wfExp_def)
apply (cut_tac g = "g" and p = "p" and a = "a" in wfforPathInGraph, auto)
done

theorem EPIsRefTwo : "p~=[] --> b ~= c -->
                       (assign (a # p) (Val (Zint n)) ref
                       (method [(b, Path p), (c, Val (Zint n))] (assign (a # [b]) (Path [c]))))"
apply (cut_tac b = "b" and p = "p" and c = "c" and n = "n" in getLEFT)
apply (simp add:refines_def implies_def method_def locdec_def assign_def seq_def end_def seq_def begin_def)
apply (rule impI)+
apply (rule allI)+
apply (rule impI)
apply (cut_tac g = "(aa, aaa, ab, ba)" and a = "a" and p = "p" and b = "b"
           and c = "c" and n = "n" in wfforLabelExpFT, auto)
apply (cut_tac g = "(aa, aaa, ab, ba)" and l = "getLabelExpF [(b, Path p), (c, Val (Zint n))]" 
                 in wfVars, auto)
apply (cut_tac g = "(aa, aaa, ab, ba)"  and p = "p" and 
               f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]" 
           and l = "b" and a = "a"  in wfPathforVars, auto)
apply (simp add:wfExp_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]"
           and l = "c" and n = "n" in getCorrectLocalValue, auto)
apply (simp add:pathInGraph_def getNodeVal_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and 
        n = "getNodeExp (Path [c]) (Vars (%l. if l = b then Path p else if l = c then Val (val.Zint n) else undefExp) (aa, aaa, ab, ba))" 
    and p = "p" and f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]"
    and l = "b" and a = "a" in wfforSwingPathVars, auto)
apply (cut_tac g = "(aa, aaa, ab, ba)" and f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]"
           and l = "c" and n = "n" in getCorrectLocalValue, auto)
apply (simp add:getNodeExp_def getNodeVal_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and m = "getNodeExp (Val (val.Zint n)) (aa, aaa, ab, ba)" and p = "p"
           and f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]"
           and l = "b" and a = "a" in sameGraphs, auto)
apply (simp add:getNodeExp_def getNodeVal_def)
apply (cut_tac g = "(aa, aaa, ab, ba)" and f = "getLabelExpF [(b, Path p), (c, Val (Zint n))]" 
           and l = "c" and n = "n" in getCorrectLocalValue, auto)
apply (simp add:getNodeExp_def getNodeVal_def)
done


end

