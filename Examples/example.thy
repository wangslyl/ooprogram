theory example imports rcos_lib 
begin

(* We first prove that the manual refinement  *)
(* d_old = [true |- a.x' = 2 OR a.x' = 3] *)
(* d_new = [true |- a.x' = 2] *)
(* is a correct refinement  *)

lemma r1_is_refinement : 
  "pp (true) (% g. % g1.((getIntOfPath [''x'', ''a'', ''this''] g1) = 2 | 
                         (getIntOfPath [''x'', ''a'', ''this''] g1) = 3)) [[''x'', ''a'', ''this'']]
  ref pp (true) (% g. % g1.((getIntOfPath [''x'' , ''a'', ''this''] g1) = 2)) [[''x'' , ''a'', ''this'']]"
  (is "pp (true) (%g. ?Q1) ?path ref pp (true) (%g. ?Q2) ?path")
proof -
  have f1 : "implies ?Q2 ?Q1" by (simp add:implies_def)
  thus ?thesis by (simp add:pp_strengthen_post)
qed

(* The proof of  *)
(* d_old = [true |- a.x' = 2] *)
(* d_new = a.x := 2 *)
(* is directly deduced by ref_pp_assign  *)
lemma r2_is_refinement : 
  "pp (true) (% g. % g1.((getIntOfPath [''x'' , ''a'', ''this''] g1) = 2)) [[''x'' , ''a'', ''this'']]
  ref 
  assign [''x'' , ''a'', ''this''] (Val (Zint 2))"
by (simp add:ref_pp_assign)

(* The proof of the manual refinement   *)
(* d_old = a.x := 2  *)
(* d_new = a.x := 1 ;  a.x := a.x + 1 *)
lemma r3_is_refinement : 
"(assign [''x'' , ''a'' , ''this''] (Val (Zint 2)))
  ref 
  (assign [''x'' , ''a'' , ''this''] (Val (Zint 1)); 
  (assign [''x'' , ''a'' , ''this''] (Plus (Path [''x'' , ''a'' , ''this'']) (Val (Zint 1)))))"
by (insert assign_end [of "[''x'' , ''a'' , ''this'']" "2" "1"], simp)


(* The proof of   *)
(* d_old = a.x := 1 ;  a.x := a.x + 1 *)
(* d_new = a.m(1) ;  a.x := a.x + 1 *)
(* follows using EPIsRefTwo and seq_ref *)
lemma r4_is_refinement : 
" (assign [''x'' , ''a'', ''this''] (Val (Zint 1)); 
   assign [''x'' , ''a'' , ''this''] (Plus (Path [''x'' , ''a'' , ''this'']) (Val (Zint 1))))
ref 
  ((method [(''this'', Path [ ''a'', ''this'']), (''v'', Val (Zint 1))] 
           (assign [''x'', ''this''] (Path [''v'']))) ; 
   assign [''x'' , ''a'' , ''this''] (Plus (Path [''x'' , ''a'' , ''this'']) (Val (Zint 1))))"
(is "(?A ; ?B) ref (?C ; ?B) ")
proof -
  have f1 : "?A ref ?C"  by (simp add:EPIsRefTwo)
  thus ?thesis by (simp add:seq_ref_left)
qed

(* We prove the final refinement  *)
(* d_old = [true |- a.x' = 2 OR a.x' = 3] *)
(* d_new = a.m(1) ; a.x := a.x + 1 *)
lemma chain_is_refinement : 
  "pp (true) (% g. % g1.((getIntOfPath [''x'', ''a'', ''this''] g1) = 2 
                       | (getIntOfPath [''x'', ''a'', ''this''] g1) = 3)) [[''x'', ''a'', ''this'']] 
  ref 
  ((method [(''this'', Path [ ''a'', ''this'']), (''v'', Val (Zint 1))] 
           (assign [''x'', ''this''] (Path [''v'']))) ; 
   assign [''x'' , ''a'' , ''this''] (Plus (Path [''x'' , ''a'' , ''this'']) (Val (Zint 1))))"
   (is "?A ref ?B")
proof - 
  let ?path = "[''x'' , ''a'', ''this'']"
  let ?C = "pp (true) (% g. % g1.((getIntOfPath ?path g1) = 2)) [?path]"
  let ?D = "assign ?path (Val (Zint 2))"
  let ?E = "(assign ?path (Val (Zint 1)) ; 
            (assign ?path (Plus (Path ?path) (Val (Zint 1)))))"
  have f1 : "?A ref ?C"  by (simp add:r1_is_refinement)
  have f2 : "?C ref ?D" by (simp add:r2_is_refinement)
  have f3 : "?D ref ?E" by (simp add:r3_is_refinement)
  have f4 : "?E ref ?B" by (simp add:r4_is_refinement)
  from f1 f2 have "?A ref ?D" by (simp add:ref_transitive [of "?A" "?C" "?D"])
  with f3 have "?A ref ?E" by (simp add:ref_transitive [of "?A" "?D" "?E"])
  with f4 show ?thesis by (simp add:ref_transitive [of "?A" "?E" "?B"])
qed


end

