theory po1 imports rcos_lib
begin

(* An application of expert pattern: *)
(* class M {bool b; m () {this.x := 1}} *)
(* class N {M x; n1 () {this.a.b.x := 1}} *)
(* class N {M x; n2 () {this.a.b.m()}} *)
(* We prove "|- this.a.b.x:=1 ref this.a.b.m()" below. *)


theorem po3IsRef : "(assign [''x'', ''b'',''a'', ''this''] (Val (Zint 1)))
             ref
             (method [(''this'', Path [''b'', ''a'', ''this''])] 
              (assign [''x'', ''this''] (Val (Zint 1))))"

apply (cut_tac p = "[''b'',''a'', ''this'']" and a = "''x''" and n = "1" and b = "''this''"
               in EPIsRefOne, auto)
done

(* class B {int x; n (int v) {this.y := v}} *)
(* contract IP of I {A a; bar() {a.b.y := 2}} *)
(* class C {A a; bar() {a.b.n(1)}} *)
(* We prove "|- this.a.b.y:=2 ref this.a.b.n(2)" below. *)


theorem po2IsRef : "(assign [''y'', ''b'',''a'', ''this''] (Val (Zint 2)))
                 ref
                    (method [(''this'', Path [''b'', ''a'', ''this'']), (''v'', Val (Zint 2))] 
                       (assign [''y'', ''this''] (Path [''v''])))"

apply (cut_tac p = "[''b'',''a'', ''this'']" and a = "''y''" and n = "2" and b = "''this''"
           and c = "''v''" in EPIsRefTwo, auto)
done


(* class B {int x; m () {this.x := 1}
                   n (int v) {this. y := v}} *)
(* contract IP of I {A a; bar() {a.b.x := 1; a.b.y :=2}} *)
(* class C {A a; bar() {a.b.m(); a.b.n(2);}} *)
(* We prove "|- this.a.b.x:=1; this.a.b.y :=2 ref this.a.b.m(); this.a.b.n(2)" below. *)
lemma seqIsRefOne : 
      "(assign [''x'', ''b'',''a'', ''this''] (Val (Zint 1)));
       (assign [''y'', ''b'',''a'', ''this''] (Val (Zint 2)))
       ref
       (method [(''this'', Path [''b'', ''a'', ''this''])] 
       (assign [''x'', ''this''] (Val (Zint 1))));
       (method [(''this'', Path [''b'', ''a'', ''this'']), (''v'', Val (Zint 2))] 
       (assign [''y'', ''this''] (Path [''v''])))"
apply (cut_tac c = "(assign [''x'', ''b'',''a'', ''this''] (Val (Zint 1)))" 
           and e = "(assign [''y'', ''b'',''a'', ''this''] (Val (Zint 2)))" 
           and d = "(method [(''this'', Path [''b'', ''a'', ''this''])] 
                    (assign [''x'', ''this''] (Val (Zint 1))))" 
           and f = "(method [(''this'', Path [''b'', ''a'', ''this'']), (''v'', Val (Zint 2))] 
                    (assign [''y'', ''this''] (Path [''v''])))" 
           in seq_ref, auto)
apply (cut_tac e = "(Val (Zint 1))" 
           and p = "[''x'', ''b'', ''a'', ''this'']" in assign_monotonic, auto)
(*ask: why can't I use the theorems in po2 and po3 directly??*)
apply (insert po3IsRef, simp)
apply (insert po2IsRef, simp)
done

(* Transitive: |-this.a.b.x':=1 ref this.a.b.m()*)
lemma TranIsRef :
      "pp (true) (% g. % g1.((getIntOfPath [''x'' , ''b'' , ''a'', ''this''] g1) = 1)) [[''x'' , ''b'' , ''a'', ''this'']]
       ref
       (method [(''this'', Path [''b'', ''a'', ''this''])] 
       (assign [''x'', ''this''] (Val (Zint 1))))"
apply (cut_tac n = "1" and p = "[''x'' , ''b'' , ''a'', ''this'']" in ref_pp_assign)
apply (insert po3IsRef)
apply (cut_tac 
    x = " pp true (%g g1. getIntOfPath [''x'', ''b'', ''a'', ''this''] g1 = 1) [[''x'', ''b'', ''a'', ''this'']] " 
and y = " assign [''x'', ''b'', ''a'', ''this''] (Val (Zint 1))" 
and z = " method [(''this'', Path [''b'', ''a'', ''this''])]
         (assign [''x'', ''this''] (Val (Zint 1)))" in ref_transitive, auto)
done



end




