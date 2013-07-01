
header {* Graphs and Graph Operations and Graph Lemmas*}

(*<*) theory graph_utl imports Main begin (*>*)

types  onode = nat
       vnode = nat
       label = string 
       mname = string
       
datatype ctype = C string | undefType
datatype val = Zint int | Bool bool | String string
(* datatype typeval = T ctype | V val *) 
datatype snode = D nat | undefSnode
datatype vertex = N onode | R snode | L vnode | undefVertex

types
       edgefun = "(vertex => label => vertex)"
       onodefun = "onode => ctype"
       vnodefun = "vnode => val"
       graph =  "edgefun * onodefun  * vnodefun * snode list"
       path = "label list"

(* An expression can be a navigation path, or a primitive value, or undefined. *)

datatype exp = Path path | Val val | undefExp
             | Plus exp exp | Minus exp exp | Times exp exp | Divide exp exp

definition getEdgeFun :: "graph => edgefun " where 
"getEdgeFun g = fst g"

definition getOnodeFun :: "graph => onodefun" where 
"getOnodeFun g = fst (snd g)"

definition getVnodeFun :: "graph => vnodefun" where 
"getVnodeFun g = fst (snd (snd g))"

definition getSnodeList :: "graph => snode list" where 
"getSnodeList g = snd (snd (snd g))"


(* We don't want to unfold the definition manually *)
declare getEdgeFun_def [simp]
declare getOnodeFun_def [simp]
declare getVnodeFun_def [simp]
declare getSnodeList_def [simp]


text{* isInVertex, checks whether the label variable is defined in the current vertex
     *}

definition isInVertex:: "edgefun => vertex => label => bool" where
"isInVertex p n v ==  p n v ~= undefVertex"

lemma tupleGraph: "g = (getEdgeFun g, getOnodeFun g, getVnodeFun g, getSnodeList g)"
apply (simp)
done

definition isNotTargetList:: "graph => bool" where
"isNotTargetList g == ALL x y l. (getEdgeFun g) x l ~= R y"


consts isUnique:: "snode list => bool" 
primrec
  "isUnique [] = True"
  "isUnique (n#l) = (if (n mem l) then False else (isUnique l))"

definition snodesAreSources :: "graph => bool" where
"snodesAreSources g ==   
  (ALL r. r mem (getSnodeList g) --> (EX l. ((getEdgeFun g) (R r) l ~= undefVertex)))"

definition snodesAreDefined :: "snode list => bool" where
"snodesAreDefined l == ALL x. x mem l --> x ~= undefSnode"


constdefs isCorrectSnode:: "graph => bool" where
"isCorrectSnode g ==
  (isUnique (getSnodeList g)) & 
  (snodesAreSources g) & 
  (isNotTargetList g) &  
   snodesAreDefined (getSnodeList g)"
  (* to think: ..(R undefSnode) l = ??? Now (R undefSnode) ~= undefVertex *)
definition isGoodFunction :: "graph => bool" where
"isGoodFunction g ==
  (ALL l.(getEdgeFun g) undefVertex l = undefVertex)
& (ALL l.(getEdgeFun g) (R undefSnode) l = undefVertex)"

constdefs wfGraph:: "graph => bool"
"wfGraph g == isCorrectSnode g & isGoodFunction g"

(* The  vertex is neither the source nor the target of some edge *)
definition vertexNotInEdges :: "edgefun => vertex => bool" where
"vertexNotInEdges p n == ALL l m. ((p n l) = undefVertex & p m l ~= n)"

definition vertexNotInGraph :: "graph => vertex => bool" where
"vertexNotInGraph g n = vertexNotInEdges (getEdgeFun g) n"

consts getFreshSnode :: "graph => snode"

lemma getFreshSnodeIsUnique_spec: "vertexNotInGraph g  (R (getFreshSnode g)) & (getFreshSnode g) ~= undefSnode"
sorry

definition createSnode :: "graph  => graph" where
"createSnode g =  (fst g, fst (snd g), fst (snd (snd g)),  (getFreshSnode g) # (snd (snd (snd g))))"

lemma createSnodeListNotEmpty: "~(getSnodeList (createSnode g) = [])"
apply (simp add: createSnode_def getSnodeList_def)
done

lemma createSnodeNotChangeOnodefun: "getOnodeFun (createSnode g) = getOnodeFun g"
apply (simp add:createSnode_def)
done

lemma createSnodeNotChangeVnodefun: "getVnodeFun (createSnode g) = getVnodeFun g"
apply (simp add:createSnode_def)
done

lemma createSnodeNotChangeEdgefun: "getEdgeFun (createSnode g) = getEdgeFun g"
apply (simp add:createSnode_def)
done


text{* @{text removeSnode}, remove the snode from the snode list, and all its associated edges from the edge list*}

definition removeSnode :: "graph => graph" where 
"removeSnode g == 
  case (getSnodeList g) of [] => g 
  | t#q => (% v. % l. (if (v = R t) then undefVertex else (getEdgeFun g) v l), getOnodeFun g, getVnodeFun g, q)"

lemma removeSnodeRemoveEdges:"getSnodeList g ~= [] ==> ~isInVertex (getEdgeFun (removeSnode g)) (R (hd (getSnodeList g))) l"
apply (simp add:isInVertex_def removeSnode_def)
apply (case_tac "getSnodeList g", auto)
done


lemma removeSnodeNotChangeOnodefun: "getOnodeFun (removeSnode g) = getOnodeFun g"
apply (simp add:removeSnode_def)
apply (case_tac "getSnodeList g", auto)
done

lemma removeSnodeNotChangeVnodefun: "getVnodeFun (removeSnode g) = getVnodeFun g"
apply (simp add:removeSnode_def)
apply (case_tac "getSnodeList g", auto)
done

lemma removeCreateNotChangeSnodeList: "getSnodeList (removeSnode (createSnode g)) = getSnodeList g"
apply (simp add:removeSnode_def)
apply (cut_tac g = "g" in createSnodeListNotEmpty)
apply (case_tac "getSnodeList (createSnode g)", auto)
apply (simp add:createSnode_def getSnodeList_def)
done

lemma removeSnodePreservesEqualSnodeList: "getSnodeList u = getSnodeList v ==>
             getSnodeList (removeSnode u) = getSnodeList (removeSnode v)"
apply (simp add:removeSnode_def)
apply (case_tac "getSnodeList v", auto)
done

lemma removeSnodePreservesGetEdges: "~(v = R (hd (getSnodeList g))) ==> (getEdgeFun (removeSnode g)) v l = (getEdgeFun g) v l"
apply (simp add:removeSnode_def)
apply (case_tac "getSnodeList g", auto)
done

lemma snodeAreRemoved: "isCorrectSnode g ==> x mem getSnodeList (removeSnode g) ==> x ~= (hd (getSnodeList g))"
apply (simp add:isCorrectSnode_def removeSnode_def, auto)
apply (case_tac "snd (snd (snd g))", auto)
done


lemma removeSnodePreservesGetSnodeList : "r mem (getSnodeList (removeSnode g)) ==> r mem getSnodeList g"
proof (simp add:removeSnode_def)
  assume h: " r mem snd (snd (snd 
           (case snd (snd (snd g)) of [] => g
            | t # q => (%v l. if v = R t then undefVertex else getEdgeFun g v l, getOnodeFun g, getVnodeFun g, q))))"
  show "r mem snd (snd (snd g))"
  proof (cases "snd (snd (snd g))")
    case Nil with h show ?thesis by simp
  next
    case Cons with h show ?thesis by (simp)
  qed
qed

lemma removeSnodePreservesSnodesAreDefined: "isCorrectSnode g ==> snodesAreDefined (getSnodeList (removeSnode g))"
proof (simp add:isCorrectSnode_def removeSnode_def)
  assume h: " isUnique (snd (snd (snd g))) & snodesAreSources g & isNotTargetList g & snodesAreDefined (snd (snd (snd g)))"
  show "snodesAreDefined
         (snd (snd (snd (case snd (snd (snd g)) of [] => g
                         | t # q =>
                             (%v l. if v = R t then undefVertex else getEdgeFun g v l, getOnodeFun g, getVnodeFun g,
                              q)))))
 "
  proof (cases "snd (snd (snd g))")
    case Nil with h show ?thesis by simp
  next
    case Cons with h show ?thesis by (simp add:snodesAreDefined_def)
  qed
qed

lemma removeSnodePreservesisNotTargetList :"isCorrectSnode g ==> isNotTargetList (removeSnode g)"
apply (simp add:isCorrectSnode_def removeSnode_def isNotTargetList_def, auto)
apply (case_tac "snd (snd (snd g))", auto)
apply (split split_if_asm, auto)
apply (split split_if_asm, auto)
done

lemma removeSnodePreservesisUnique : "isCorrectSnode g ==> isUnique (getSnodeList (removeSnode g)) "
apply (simp add:isCorrectSnode_def removeSnode_def Let_def, auto) 
apply (case_tac "getSnodeList g", auto)
apply (split split_if_asm, auto)
done

lemma removeSnodePreservessnodesAreSources : "isCorrectSnode g ==> snodesAreSources (removeSnode g)"
apply (simp add: isCorrectSnode_def snodesAreSources_def, auto)
apply (cut_tac g=g and r=r in removeSnodePreservesGetSnodeList, auto)
apply (drule spec mp, auto)
apply (simp add:removeSnode_def)
apply (case_tac "snd (snd (snd g))", auto)
done

theorem removeSnodePreservesisCorrectSnode: "isCorrectSnode g ==> isCorrectSnode (removeSnode g)"
apply (cut_tac g = "g" in removeSnodePreservesisNotTargetList, auto)
apply (cut_tac g = "g" in removeSnodePreservesisUnique, auto)
apply (cut_tac g = "g" in removeSnodePreservessnodesAreSources, auto)
apply (cut_tac g = "g" in removeSnodePreservesSnodesAreDefined, auto)
apply (simp add:isCorrectSnode_def)
done

lemma removeSnodePreservesisGoodFunction: "wfGraph g ==> isGoodFunction (removeSnode g)"
apply (simp add:wfGraph_def isCorrectSnode_def isGoodFunction_def removeSnode_def, auto)
apply (case_tac "snd (snd (snd g))", auto)+
done

theorem wfRemoveSnode: "wfGraph g ==> wfGraph (removeSnode g)"
apply (cut_tac g = "g" in removeSnodePreservesisGoodFunction, auto)
apply (simp add:wfGraph_def removeSnodePreservesisCorrectSnode)
done

text{*swingEdge, delete the swung edge, and then add an edge.*}

definition swingEdge:: " vertex => label => vertex => graph => graph" where
"swingEdge n x m g == (if ((getEdgeFun g) n x) = undefVertex then g 
                       else if m = undefVertex then g 
                       else ((% v. % l. (if (v = n & l = x) then m else  ((getEdgeFun g) v l))), 
                                getOnodeFun g, getVnodeFun g, getSnodeList g))"

consts getSnodeOfVarEL :: "edgefun => label => snode list => snode" 
primrec
"getSnodeOfVarEL edges l [] = undefSnode"
"getSnodeOfVarEL edges l (t#q) = (if (isInVertex edges (R t) l) then t else (getSnodeOfVarEL edges l q))" 

definition getSnodeOfVar:: "label => graph => snode" where
"getSnodeOfVar l g == getSnodeOfVarEL (getEdgeFun g) l (getSnodeList g)"

(* The navigation expression x.y.z is represented by the REVERSE path [z, y, x] *)

definition getSnodeOfPath :: "path => graph => snode" where
"getSnodeOfPath l g == (if l = [] then undefSnode else (getSnodeOfVar (last l) g))"

  (* getOwner: returns the parent of the vertex of the path. *)
consts getOwner :: "path => graph => vertex" 
primrec
"getOwner [] g = undefVertex "
"getOwner (x#t) g =  (if t = [] then (R (getSnodeOfVar x g))  else 
                         ((getEdgeFun g) (getOwner t g) (hd t)))"

definition getVertexPath :: "path => graph => vertex" where
"getVertexPath p g == (if p = [] then undefVertex else ((getEdgeFun g) (getOwner p g) (hd p)))" 

lemma gVPisAfterOwner : " p ~= [] ==> getVertexPath p g  = fst g (getOwner p g) (hd p)"
  by (simp add:getVertexPath_def)

lemma ownerIsgVPprefix : "tl p ~=[] ==>  getOwner p g  = getVertexPath (tl p) g"
by (induct p, auto, simp add:gVPisAfterOwner)

lemma gVPisNext : "p ~= [] ==> getVertexPath (a#p) g = (getEdgeFun g) (getVertexPath p g) a"
by (insert gVPisAfterOwner [of "a#p" "g"], insert ownerIsgVPprefix [of "a#p" "g"], simp)

lemma getVertexPathIsNotNewSnode:"getVertexPath p g ~= R (hd (getSnodeList (createSnode g)))"
apply (simp add:createSnode_def)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def getVertexPath_def)
done

definition swingPath :: "path => vertex => graph => graph" where
"swingPath p n g == (if p = [] then g else swingEdge (getOwner p g) (hd p) n g)"

lemma nodeIsNotNewSnode: "isInVertex (getEdgeFun (swingPath p m g)) n s
                        ==> ~ (n = R (hd (getSnodeList (createSnode g))))"
apply (simp add:isInVertex_def createSnode_def, auto)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def swingPath_def)
apply (split split_if_asm, auto)
apply (simp add:swingEdge_def)
apply (split split_if_asm, auto)+
done

lemma newSnodeNotInGraph: "~isInVertex (getEdgeFun g) (R (hd (getSnodeList (createSnode g)))) l"
apply (simp add:isInVertex_def createSnode_def)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec, auto)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def)
done

lemma swingEdgeNotChangeSnodeList: "getSnodeList (swingEdge m x n g) = getSnodeList g"
by (simp add:swingEdge_def)


(* This lemma is also true with "~=undefVertex" replaced by "=z" *)
lemma sublemmaIsInVertexLeft1 : 
  " (a ~= x | b ~=y) ==> isInVertex ((getEdgeFun g)) x y ==> 
    isInVertex (getEdgeFun (swingEdge a b n g)) x y"
by (simp add:isInVertex_def swingEdge_def)

lemma lemmaisInVertexLeft : assumes h : " isInVertex (getEdgeFun g) v l"
  shows "isInVertex (getEdgeFun (swingEdge m x n g)) v l"
proof - 
  from h show "isInVertex (getEdgeFun (swingEdge m x n g)) v l"
  proof (cases "m = v & x =  l")
    case False with sublemmaIsInVertexLeft1 [of m v x l g n] h show ?thesis by (simp add:isInVertex_def)
  next
    case True with h show ?thesis  by (simp add:isInVertex_def swingEdge_def)
  qed
qed


lemma swingPathPreservesEdgefun: "isInVertex (getEdgeFun g) v l ==> isInVertex (getEdgeFun (swingPath p n g)) v l" 
apply (simp add:isInVertex_def swingPath_def, auto)
apply (cut_tac g = "g" and v = "v" and l = "l" and m = "getOwner p g" and x = "hd p" and n = "n" in lemmaisInVertexLeft)
apply (simp add:isInVertex_def, auto)
apply (simp add:isInVertex_def)
done  

lemma sublemmaIsInVertexRight1 : "(a ~= x | b ~=y) ==> isInVertex (getEdgeFun (swingEdge a b n g)) x y
                                  ==>  isInVertex (getEdgeFun g) x y"
apply (simp add:isInVertex_def swingEdge_def, auto)
apply (case_tac "fst g a b=undefVertex", auto)
apply (case_tac "n=undefVertex", auto)
apply (split split_if_asm, simp)
apply (case_tac "n=undefVertex", auto)
done

lemma lemmaisInVertexRight : 
  "isInVertex (getEdgeFun (swingEdge m x n g)) v l ==> isInVertex (getEdgeFun g) v l "
apply (simp add:isInVertex_def, auto)
apply (case_tac "m = v & x =  l")
apply (simp add:swingEdge_def)
apply (cut_tac a = "m" and b = "x"  and x = "v"  and y = "l" 
           and g = "g" and n="n" in sublemmaIsInVertexRight1, auto)
apply (simp add:isInVertex_def)+
done

lemma swingEdgeNotChangeGetSnodeOfVarEL : 
  "getSnodeOfVarEL (getEdgeFun g) l rl = getSnodeOfVarEL (getEdgeFun (swingEdge m x n g)) l rl"
apply (induct rl, auto)
apply (cut_tac g="g" and v="R a" and l="l" and m="m" and x="x" and n="n" in lemmaisInVertexLeft, auto)
apply (cut_tac g="g" and v="R a" and l="l" and m="m" and x = "x" and n="n" in lemmaisInVertexRight, auto)
done

lemma swingEdgeNotChangeGetSnodeOfVar: 
" getSnodeOfVar l (swingEdge m x n g) = getSnodeOfVar l g"
apply (simp add:getSnodeOfVar_def)
apply (cut_tac g = "g" and m = "m" and x="x" and n = "n" in swingEdgeNotChangeSnodeList, auto)
apply (cut_tac g = "g" and l="l" and rl = "snd (snd (snd g))" and m = "m" and x="x" 
  and n = "n" in swingEdgeNotChangeGetSnodeOfVarEL, auto)
done

lemma swingPathPreservesUnswungEdges:
"~(n = getOwner p g) | ~(l = hd p) ==> getEdgeFun (swingPath p m g) n l = (getEdgeFun g) n l"
apply (simp add:swingPath_def swingEdge_def, auto)
done

consts getListOfNodesInit :: "path => graph => vertex => vertex list" 
primrec 
"getListOfNodesInit [] g r = [r]"
"getListOfNodesInit (x#t) g r = ((getEdgeFun g) (hd (getListOfNodesInit t g  r)) x) #  
  (getListOfNodesInit t g r)"


definition getListOfNodes :: "path => graph => vertex list" where
"getListOfNodes p g == if (p = []) then [] else getListOfN
odesInit p g (R (getSnodeOfPath p g))"

definition isGoodPath :: "path => graph => bool" where 
  "isGoodPath p g == 
  p = []  | tl p = [] | (p ~= [] & tl p ~= [] & (tl (tl p)) = [] &  (getOwner p g ~= (R (getSnodeOfPath p g)))) | 
  ( tl (tl p)) ~= [] &  ~((getOwner p g)  mem (getListOfNodes (tl (tl p)) g))"

definition pathInGraph:: "path => graph => bool" where
"pathInGraph p g == getVertexPath p g ~= undefVertex"

lemma pathInGraphImpliesNotSnodeNode: "ALL x. wfGraph g ==> pathInGraph p g ==> getVertexPath p g ~= R x"
apply (simp add:wfGraph_def pathInGraph_def, auto)
apply (simp add:isCorrectSnode_def isNotTargetList_def getVertexPath_def, auto)
apply (split split_if_asm, auto)
done

lemma pathInGraphImpliesNotEmpty: "pathInGraph p g ==> p ~= []"
apply (simp add: pathInGraph_def getVertexPath_def, auto)
done

lemma pathInGraphbyExtension: "wfGraph g ==> p ~=[] ==> pathInGraph (a # p) g ==> pathInGraph p g"
apply (simp add:wfGraph_def isGoodFunction_def pathInGraph_def)
apply (cut_tac a = "a" and p = "p" and g = "g" in gVPisNext, auto)
done
  
definition wfPath :: "path => graph => bool" where
"wfPath p g == isGoodPath p g & pathInGraph p g"

definition wfPathl :: "path list => graph => bool" where
"wfPathl l g == (ALL p. p mem l --> wfPath p g)"

definition equivPrefix :: "path => graph => graph => bool" where
"equivPrefix p h g == ALL n l. n mem (getListOfNodes p g) -->
  (getEdgeFun h) n l = (getEdgeFun g) n l"

definition sameSnodes :: "path => graph => graph => bool" where
"sameSnodes p h g == getSnodeOfPath p h = getSnodeOfPath p g"

lemma sameSnodesPreserved : "sameSnodes (a # p) h g ==> sameSnodes p h g"
  by (simp add:sameSnodes_def getSnodeOfPath_def, auto)

lemma PEPreservesGetSnodeOfP : "p ~= [] ==> getSnodeOfPath p g = getSnodeOfPath (a#p) g"
  by (simp add:getSnodeOfPath_def)

lemma ListOfNodesMonotonic : "n mem getListOfNodes p g ==> n mem getListOfNodes (a # p) g"
apply (simp add:getListOfNodes_def, auto)
apply (split split_if_asm, auto)
apply (cut_tac g="g" and p="p" and a="a" in PEPreservesGetSnodeOfP, simp)
apply (case_tac p, auto)
done

lemma equivPrefixPreserved : "equivPrefix (a # p) h g ==> equivPrefix p h g"
apply (simp add:equivPrefix_def, auto)
apply (cut_tac p = "p" and n = "n" and g = "g" and a = "a" in ListOfNodesMonotonic, auto)
done

lemma swingPathPreservesSameSnodes : 
 "sameSnodes p (swingPath p n g) g"
apply (simp add:sameSnodes_def getSnodeOfPath_def swingPath_def, auto)
apply (cut_tac g = "g" and m = "getOwner p g" and x = "hd p" and n = "n" and l = "last p"
             in swingEdgeNotChangeGetSnodeOfVar, auto)
done

lemma swingPathPreservesEquivPrefix : 
 "isGoodPath p g  ==> equivPrefix  (tl (tl p)) (swingPath p n g) g"
apply (simp add:equivPrefix_def getListOfNodes_def isGoodPath_def, auto)
apply (simp add:swingPath_def swingEdge_def, auto)
done

lemma gVPIsHdOfLON : "p ~= [] ==> getVertexPath p g = hd (getListOfNodes p g)"
apply (induct p)
apply (simp add:getVertexPath_def getListOfNodes_def getSnodeOfPath_def)
apply (case_tac p)
apply (simp add:getVertexPath_def getListOfNodes_def getSnodeOfPath_def)
apply (cut_tac g="g" and a="a" and p="p" in gVPisNext, simp)
apply (simp add:getListOfNodes_def getSnodeOfPath_def)
done

lemma LONsNotEmpty: "getListOfNodesInit p g n ~= []" 
apply (induct p, auto)
done

lemma HdMemOfNotEmptyList: "l ~= [] ==> hd l mem l"
apply (induct l, auto)
done

lemma equivPrefixEqualGetListofNodes : "sameSnodes p h g ==> equivPrefix p h g 
                                    ==> getListOfNodes p g = getListOfNodes p h"
apply (simp add:getListOfNodes_def, auto)
apply (induct p, auto) 
apply (case_tac "p = []", auto)
apply (simp add:sameSnodes_def equivPrefix_def)
apply (simp add:getListOfNodes_def)
apply (cut_tac h="h" and g="g" and p="p" and a="a" in sameSnodesPreserved, auto)
apply (cut_tac h="h" and g="g" and p="p" and a="a" in equivPrefixPreserved, auto)
apply (simp add:equivPrefix_def)
apply (cut_tac g="h" and p="p" and a="a" in PEPreservesGetSnodeOfP, auto)
apply (cut_tac g="g" and p="p" and a="a" in PEPreservesGetSnodeOfP, auto)
apply (simp add:getListOfNodes_def)
prefer 2
apply (case_tac "p = []", auto)
apply (simp add:sameSnodes_def)
apply (cut_tac h="h" and g="g" and p="p" and a="a" in sameSnodesPreserved, auto)
apply (cut_tac h="h" and g="g" and p="p" and a="a" in equivPrefixPreserved, auto)
apply (cut_tac g="h" and p="p" and a="a" in PEPreservesGetSnodeOfP, auto)
apply (cut_tac g="g" and p="p" and a="a" in PEPreservesGetSnodeOfP, auto)
apply (cut_tac p = "p" and g = "h" and  n = "R (getSnodeOfPath (a # p) h)" in LONsNotEmpty)
apply (subgoal_tac " hd (getListOfNodesInit p h (R (getSnodeOfPath (a # p) h)))
                     mem getListOfNodesInit p h (R (getSnodeOfPath (a # p) h))", auto)
apply (cut_tac l = "getListOfNodesInit p h (R (getSnodeOfPath (a # p) h))" in HdMemOfNotEmptyList, auto)
done


lemma TlEqual : "tl (tl p) ~= [] ==> sameSnodes p h g ==> equivPrefix (tl (tl p)) h g
             ==> (getEdgeFun g) (hd (getListOfNodes (tl (tl p)) g)) (hd (tl p)) = 
                 (getEdgeFun h) (hd (getListOfNodes (tl (tl p)) h)) (hd (tl p))"
apply (subgoal_tac "sameSnodes (tl (tl p)) h g")
apply (cut_tac g="g" and h="h" and p="tl (tl p)" in equivPrefixEqualGetListofNodes, auto)
apply (simp add:equivPrefix_def)
apply (subgoal_tac "(hd (getListOfNodes (tl (tl p)) g)) mem (getListOfNodes (tl (tl p)) g)", auto)
apply (simp add:getListOfNodes_def)
apply (cut_tac p = "(tl (tl p))" and g = "h" and  n = "R (getSnodeOfPath (tl (tl p)) h)" in LONsNotEmpty)
apply (cut_tac l = "getListOfNodesInit (tl (tl p)) h (R (getSnodeOfPath (tl (tl p)) h))" in HdMemOfNotEmptyList, auto)
apply (cut_tac h = "h" and g = "g" and a = "hd p" and p = "tl p" in sameSnodesPreserved)
apply (subgoal_tac "p ~= []", auto)
apply (cut_tac h = "h" and g = "g" and a = "hd (tl p)" and p = "tl (tl p)" in sameSnodesPreserved, auto)
apply (subgoal_tac "tl p ~= []", auto)
done


lemma TlIsOwner : "tl (tl p) ~= [] ==> getEdgeFun g(hd (getListOfNodes (tl (tl p)) g)) (hd (tl p)) = getOwner  p g "
apply (simp add:getListOfNodes_def getSnodeOfPath_def)
apply (subgoal_tac "getOwner (tl p) g= hd (getListOfNodes (tl (tl p)) g)")
apply (subgoal_tac "((getEdgeFun g) (getOwner (tl p) g) (hd (tl p))) = getOwner p g")  
apply (simp add:getListOfNodes_def getSnodeOfPath_def)
apply (cut_tac g=g and p=p in ownerIsgVPprefix, auto)
apply (cut_tac g=g and p="tl p" in gVPisAfterOwner, auto)
apply (cut_tac g=g and p="tl p" in ownerIsgVPprefix, auto)
apply (cut_tac g=g and p="tl (tl p)" in gVPIsHdOfLON, auto)
done

lemma snodeIsOwner : "tl p = [a] ==> getOwner p g = (getEdgeFun g) (R (getSnodeOfPath p g)) (hd (tl p))"
apply (case_tac p, simp)
apply (simp add:getSnodeOfPath_def)
done

lemma equivPrefixEqualGetOwner : "tl (tl p) ~= [] ==> sameSnodes p h g ==> 
                                  equivPrefix (tl (tl p)) h g ==> getOwner p g = getOwner p h"
apply (case_tac "tl p")
apply (simp add:sameSnodes_def getSnodeOfPath_def)
apply (case_tac "p", simp)
apply simp
apply (case_tac "tl (tl p)")
prefer 2
apply (cut_tac p="p" and g="g" in TlIsOwner, simp)
apply simp
apply (cut_tac p="p" and g="h" in TlIsOwner, simp)
apply simp
apply (cut_tac p="p" and g="g" and h="h" in TlEqual, auto)
done

lemma swingPathPreservesGetOwner_b : 
       "isGoodPath p g ==> tl p = [a] ==> getOwner p g = getOwner p (swingPath p n g)"
apply (cut_tac p = "p" and n = "n" and g = "g" in swingPathPreservesSameSnodes)
apply (cut_tac g=g and p=p and a=a in snodeIsOwner, simp)
apply (cut_tac g = "swingPath p n g" and p = "p" and a = "a" in snodeIsOwner, simp)
apply (simp add:sameSnodes_def)
apply (subgoal_tac " (R (getSnodeOfPath p g)) ~= getOwner p g")
apply (cut_tac n = "(R (getSnodeOfPath p (swingPath p n g)))" and g = "g" and p = "p" and l = "a" and m = "n" 
              in swingPathPreservesUnswungEdges, auto)
apply (simp add:isGoodPath_def)
done

lemma tlsameSnodes : "sameSnodes p h g ==> sameSnodes (tl (tl p)) h g"
apply (case_tac "p = []")
apply (simp add:sameSnodes_def getSnodeOfPath_def)
apply (case_tac "tl p = []")
apply (simp add:sameSnodes_def getSnodeOfPath_def)
apply (subgoal_tac "sameSnodes (tl p) h g")
apply (cut_tac h=h and g=g and a="hd (tl p)" and p="tl (tl p)" in sameSnodesPreserved, auto)
apply (cut_tac h=h and g=g and a="hd p" and p="tl p" in sameSnodesPreserved, auto)
done

lemma swingPathPreservesGetOwner : "
   wfGraph g ==> wfPath p g ==> getOwner p (swingPath p n g) = getOwner p g"
  apply (simp add:wfGraph_def wfPath_def isCorrectSnode_def, auto)
  apply (cut_tac g = "g" and p = "p" in pathInGraphImpliesNotEmpty, auto)
  apply (simp add:pathInGraph_def)
  apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesSameSnodes)
  apply (case_tac "tl p")
  apply (simp add:sameSnodes_def getSnodeOfPath_def)
  apply (case_tac p, auto)
  apply (case_tac "tl (tl p)")
  apply (cut_tac p=p and g=g and n="n" and a="a" in swingPathPreservesGetOwner_b, auto)
  apply (cut_tac g="g" and p="p" in swingPathPreservesEquivPrefix, auto)
  apply (cut_tac g="g" and p="p" and h="swingPath p n g" in equivPrefixEqualGetOwner, auto)
done

lemma newSnodeIsNotOwner: "R (getFreshSnode g) ~= getOwner p g"
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec, auto)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def)
apply (induct p, auto)
apply (split split_if_asm, auto)
apply (simp add:getSnodeOfVar_def)
apply (induct "snd (snd (snd g))", auto)
apply (simp add:isInVertex_def)
apply (split split_if_asm, auto)
done


lemma newSnodeNotInSwungGraph: "~isInVertex (getEdgeFun (swingPath p n g)) (R (hd (getSnodeList (createSnode g)))) l"
apply (simp add:isInVertex_def createSnode_def)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec, auto)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def)
apply (case_tac "R (getFreshSnode g) ~= getOwner p g")
apply (cut_tac g = "g" and p = "p" and m = "n" and n = "R (getFreshSnode g)" 
       and l = "l" in swingPathPreservesUnswungEdges, auto)
apply (cut_tac g = "g" and p = "p" in newSnodeIsNotOwner, auto)
done

lemma snodeEmptyImpliesundefVertex : "isGoodFunction g ==> (getSnodeList g) = [] ==> ~pathInGraph p g"
apply (simp add:pathInGraph_def getVertexPath_def,auto)
apply (induct p, auto)
apply (simp add:getSnodeOfVar_def)
apply (simp add:isGoodFunction_def)+
done

lemma defVertexImpliesSnodeisNotEmpty: 
      "isGoodFunction g ==> pathInGraph p g ==> (getSnodeList g) ~= []"
apply (case_tac "getSnodeList g = []", auto)
apply (cut_tac g = "g" and p = "p" in snodeEmptyImpliesundefVertex, auto)
done

theorem swingPathChangeVertex : "wfGraph g ==> wfPath p g ==> n ~= undefVertex ==>
                                 getVertexPath p (swingPath p n g) = n"
apply (cut_tac g="g" and p="p" and n="n" in swingPathPreservesGetOwner, auto)
apply (simp add:wfGraph_def isCorrectSnode_def wfPath_def, auto)
apply (cut_tac g = "g" and p = "p" in pathInGraphImpliesNotEmpty, auto)
apply (simp add:pathInGraph_def getVertexPath_def swingPath_def swingEdge_def) 
done


lemma swingPathChangeEdge: 
  "n ~= undefVertex ==> pathInGraph p g ==> fst (swingPath p n g)(getOwner p g) (hd p) = n"              
apply (subgoal_tac "swingPath p n g = swingEdge (getOwner p g) (hd p) n g")
apply (subgoal_tac " fst (swingEdge (getOwner p g) (hd p) n g)(getOwner p g) (hd p) = n", simp)
apply (simp add:swingEdge_def)
apply (cut_tac g = "g" and p = "p" in pathInGraphImpliesNotEmpty, auto)
apply (simp add: pathInGraph_def getVertexPath_def)
apply (simp add:swingPath_def)
apply (cut_tac g = "g" and p = "p" in pathInGraphImpliesNotEmpty, auto)
done

lemma swingPathNotChangeSnodeList: "getSnodeList (swingPath p n g) = getSnodeList g" 
apply (simp add:swingPath_def)
apply (cut_tac g = "g" and m= "getOwner p g" and x = "hd p" and n = "n"
       in swingEdgeNotChangeSnodeList, auto) 
done

lemma swingPathNotChangeOnodefun: "getOnodeFun (swingPath p n g) = getOnodeFun g"
apply (simp add:swingPath_def swingEdge_def)
done

lemma swingPathNotChangeVnodefun: "getVnodeFun (swingPath p n g) = getVnodeFun g"
apply (simp add:swingPath_def swingEdge_def)
done

lemma swingEdgePreservesIsUnique: "isUnique (getSnodeList g) ==> isUnique (getSnodeList (swingEdge a b n g))"
apply (cut_tac g = "g" and m = "a" and x = "b" and n = "n" in swingEdgeNotChangeSnodeList, auto)
done

lemma swingPathPreservesIsUnique: "isUnique (getSnodeList g) ==> isUnique (getSnodeList (swingPath p n g))"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathNotChangeSnodeList, auto)
done

lemma swingEdgePreservesSnodesAreDefined: "snodesAreDefined (getSnodeList g) ==> 
                                          snodesAreDefined (getSnodeList (swingEdge a b n g))"
apply (cut_tac g = "g" and m = "a" and x = "b" and n = "n" in swingEdgeNotChangeSnodeList, auto)
done

lemma swingPathPreservesSnodesAreDefined: "snodesAreDefined (getSnodeList g) ==> 
                                          snodesAreDefined (getSnodeList (swingPath p n g))"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathNotChangeSnodeList, auto)
done

lemma swingEdgePreservesSnodesAreSources:"snodesAreSources g ==> snodesAreSources (swingEdge a b n g)"
apply (simp add:snodesAreSources_def, auto)
apply (cut_tac g = "g" and m = "a" and x = "b" and n = "n" in swingEdgeNotChangeSnodeList,auto)
apply (drule spec mp, auto)
apply (cut_tac g = "g" and v = "R r" and l = "l" and m = "a" and x = "b" and n = "n" 
       in lemmaisInVertexLeft, auto)
apply (simp add:isInVertex_def)+
apply auto
done

lemma swingPathPreservesSnodesAreSources:"snodesAreSources g ==> snodesAreSources (swingPath p n g)"
apply (simp add:swingPath_def)
apply (case_tac "p = []", auto)
apply (cut_tac n = "n" and g = "g" and a = "getOwner p g" and b = "hd p" and n = "n" 
       in swingEdgePreservesSnodesAreSources, auto)
done

lemma  swingPathPreservesisNotTargetList:
       "ALL x. n ~= R x ==> isNotTargetList g ==> isNotTargetList (swingPath p n g)"
apply (simp add:isNotTargetList_def swingPath_def swingEdge_def)
done

lemma swingPathPreservesisGoodFunction: 
        "wfGraph g ==> isGoodFunction (swingPath p n g)"
apply (simp add:wfGraph_def isGoodFunction_def swingPath_def,auto)
apply (simp add:swingEdge_def)
apply (simp add:swingEdge_def, auto)
done

theorem wfswingPath: "ALL x. n ~= R x ==> wfGraph g ==> wfGraph (swingPath p n g)"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesisGoodFunction, auto)
apply (simp add:wfGraph_def isCorrectSnode_def, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesIsUnique, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesSnodesAreSources, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesisNotTargetList, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesSnodesAreDefined, auto)
done

theorem swingPathTransitive: 
          "wfGraph g ==> wfPath p g ==> n ~= undefVertex ==> m ~=undefVertex  ==> 
           swingPath p m  (swingPath p n g)= swingPath p m g"
apply (cut_tac g = "g" and p = "p" in defVertexImpliesSnodeisNotEmpty, auto)
apply (simp add:wfGraph_def)
apply (simp add:wfPath_def)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesGetOwner, auto)
apply (simp add:swingPath_def, auto)
apply (simp add:swingEdge_def, auto)
apply (simp add:expand_fun_eq)
done

  (*It returns 0 for the vertex which is not int. --to think*)

definition getInt :: "vertex => graph => int" where
"getInt v g == case v of
   (L n) => (case (getVnodeFun g n) of (Zint x) => x | _ => 0)
  | _ => 0
"

definition getIntOfPath :: "path => graph => int" where
"getIntOfPath p g ==  getInt (getVertexPath p g) g"

definition getString :: "vertex => graph => string" where 
"getString v g == case v of 
    (L n) => (case (getVnodeFun g n) of (String x) => x | _ => [])
  | _ => []"
  
definition getStringOfPath :: "path => graph => string" where 
"getStringOfPath p g ==  getString (getVertexPath p g) g"


definition getBool :: "vertex => graph => bool" where 
"getBool v g == case v of 
   (L n) => (case (getVnodeFun g n) of (Bool x) => x | _ => False)
  | _ => False
  "
definition getBoolOfPath :: "path => graph => bool" where 
"getBoolOfPath p g ==  getBool (getVertexPath p g) g"

consts getVnodeFromVal :: "val => vnode"

lemma getVnodeFromVal_spec : "(getVnodeFun g) (getVnodeFromVal n) =  n"
sorry

definition getNodeVal :: "val => vertex" where
"getNodeVal v == (L (getVnodeFromVal v))" 

(* Check if a node is in the edge list, defined for add new object *)
definition NodeNotInEdges :: "onode => edgefun => bool" where
"NodeNotInEdges n p == ALL l m. ((p (N n) l) = undefVertex & p m l ~= N n)"

(* Check if a node is just added into a graph for object creation (1, add a new node; 2, swing a path to it; 3, add *)
(* the attributes of the new node), before attaching attributes to it *)

definition NodeNotHasOutEdges:: "onode => edgefun => bool" where
"NodeNotHasOutEdges n p == ALL l. ((p (N n) l) = undefVertex)"

definition NodeNotInGraph :: "onode => graph => bool" where
"NodeNotInGraph n g = NodeNotInEdges n (getEdgeFun g)"

definition NodeNewInGraph :: "onode => graph => bool" where
"NodeNewInGraph n g = NodeNotHasOutEdges n (getEdgeFun g)"

(* Get a new node for a new created object. It's not vnode, and not in the previous graph *)

consts getNodeFromType :: "ctype => graph => onode"

  (* ??? Why is it wrong????? *)
lemma  getNodeFromType_spec : 
  "let n = getNodeFromType c g in
       (NodeNotInGraph n g) & getOnodeFun g n = c"
sorry

  (* Test *)
(* definition edges :: "edgefun" where *)
(* "edges v l = case v of   (N n) => (N 12) | *)
(*                          (L k) => undefVertex | *)
(*                          (R r) => (if (r = undefSnode) then undefVertex else (N 12))" *)

lemma getNodeFromTypeIsNotUndef : "N (getNodeFromType c g) ~= undefVertex"
apply (cut_tac g = "g" and c = "c" in getNodeFromType_spec, auto)
done

(* getNodeFromType implies NodeNewInGraph *)
lemma getNodeFromTypeNewIG: "NodeNewInGraph (getNodeFromType s g) g"
apply (simp add:NodeNewInGraph_def NodeNotHasOutEdges_def, auto)
apply (cut_tac g = "g" and c = "s" in getNodeFromType_spec)
apply (simp add:Let_def NodeNotInGraph_def NodeNotInEdges_def)
done

theorem sPCV_Int : " 
  wfGraph g ==> wfPath p g ==>
  getIntOfPath p (swingPath p (getNodeVal (Zint  n)) g) = n"
proof -
  assume h1 : "wfGraph g"
  assume h2 : "wfPath p g"
  have f3 : "getNodeVal (Zint n) ~= undefVertex" by (simp add:getNodeVal_def)
  with h1 h2 have f2 : "(getVertexPath p (swingPath p (getNodeVal (Zint n)) g)) = (getNodeVal (Zint n))"
    by (simp add:swingPathChangeVertex)
  from getVnodeFromVal_spec [of "(swingPath p (L (getVnodeFromVal (val.Zint n))) g)" "Zint n"] 
  have f4 : "getInt (getNodeVal (Zint n)) (swingPath p (getNodeVal (Zint n)) g) = n" 
    by (simp add:getInt_def getNodeVal_def)
  with f2 have f1 : "getInt (getVertexPath p (swingPath p (getNodeVal (Zint n)) g)) (swingPath p (getNodeVal (Zint n)) g)  = n" by simp
  thus ?thesis by (simp add:getIntOfPath_def)
qed

lemma createSnodePreservesGetSnodeOfVar: "getSnodeOfVar a g = getSnodeOfVar a (createSnode g)"
apply (simp add:getSnodeOfVar_def createSnode_def, auto)
apply (simp add:isInVertex_def)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def)
done

lemma createSnodePreservesGetOwner: "getOwner p g = getOwner p (createSnode g)"
apply (simp add:createSnode_def)
apply (induct p, auto)
apply (cut_tac g = "g" and a = "a" in createSnodePreservesGetSnodeOfVar, auto)
apply (simp add:createSnode_def)
done

lemma createSnodeNotChangeGetVertexP: "getVertexPath p g = getVertexPath p (createSnode g)"
apply (simp add:createSnode_def getVertexPath_def, auto)
apply (cut_tac g = g and p = p in createSnodePreservesGetOwner, auto)
apply (simp add:createSnode_def)
done

(* Definitions and properties for expressions *)

definition isIntPath :: "path => graph => bool" where
"isIntPath p g == case (getVertexPath p g) of
                              (L n) => (case (getVnodeFun g n) of (Zint x) => True | _ => False)
                             | _ => False"

definition isIntVal :: "val => bool" where
"isIntVal v == case v of (Zint n) => True
                        | _ => False"

primrec isIntExp :: "exp => graph => bool" where
"isIntExp (Path p) g  = isIntPath p g"|
"isIntExp (Val v) g = isIntVal v"|
"isIntExp undefExp g  = False"|
"isIntExp (Plus e f) g = (isIntExp e g & isIntExp f g)" |
"isIntExp (Minus e f) g = (isIntExp e g & isIntExp f g)" |
"isIntExp (Times e f) g = (isIntExp e g & isIntExp f g)" |
"isIntExp (Divide e f) g = (isIntExp e g & isIntExp f g)" 

definition wfExp :: "exp => graph => bool" where
"wfExp e g == case e of Path p => (pathInGraph p g)
                      | Val v => True
                      | undefExp => False
                      | (Plus e f) => isIntExp e g & isIntExp f g
                      | (Minus e f) => isIntExp e g & isIntExp f g
                      | (Times e f) => isIntExp e g & isIntExp f g
                      | (Divide e f) => isIntExp e g & isIntExp f g"

  (* Assumption 'isIntExp' is required for invoking this method!*)
primrec getIntOfExp :: "exp => graph => int" where
"getIntOfExp (Path p) g  = getIntOfPath p g"|
"getIntOfExp (Val v) g = (case v of (Zint n) => n | _ => 0)"|
"getIntOfExp undefExp g = 0"| 
"getIntOfExp (Plus e f) g = (getIntOfExp e g) + (getIntOfExp f g)" |
"getIntOfExp (Minus e f) g = (getIntOfExp e g) - (getIntOfExp f g)" |
"getIntOfExp (Times e f) g = (getIntOfExp e g) * (getIntOfExp f g)" |
"getIntOfExp (Divide e f) g = (getIntOfExp e g) div (getIntOfExp f g)" 

types
labelValF = "label => val"
labelVerF = "label => vertex"

(* More general than labelValF; The initial values of variables can be expressions, not just constants. *) 
types
labelExpF = "label => exp"

definition wflabelExpF :: " labelExpF => graph => bool" where
"wflabelExpF p g ==  (EX l. p l ~= undefExp) & 
                     (ALL l. (p l = undefExp | wfExp (p l) g))"

  (* !!!Important: This Lemma holds only when getVnodeFun satisfies uniqueness such that,*) 
  (* getVnodeFun g m = getVnodeFun g n, then m = n. At the moment, I am not sure whether it is necessary.*)
(* lemma "isIntExp (Path p) g ==> getNodeVal (Zint (getIntOfPath p g)) = getVertexPath p g" *)
(* apply (simp add:getNodeVal_def isIntExp_def isIntPath_def) *)
(* apply (cut_tac g = g and n = "Zint (getIntOfPath p g)" in getVnodeFromVal_spec) *)
(* apply (simp add:getIntOfPath_def getInt_def) *)
(* apply (case_tac "getVertexPath p g", auto) *)
(* apply (case_tac "fst (snd (snd g)) nat", auto) *)
(* done *)

definition valToNode :: "labelValF => labelVerF" where
"valToNode p == %l. getNodeVal(p l)"

(* Given a graph and an expression (a path or a value), we can get its node *)
(* in the graph. *)
definition getNodeExp :: " exp => graph => vertex" where
"getNodeExp e g == case e of (Val v) => getNodeVal v
                            |(Path p) => getVertexPath p g
                            | undefExp => undefVertex
                            | _ => getNodeVal (Zint (getIntOfExp e g))
                           " 

definition expToNode :: "labelExpF => graph => labelVerF" where
"expToNode p g == %l. getNodeExp (p l) g" 

lemma wfExpIsNotUndef: "wfExp e g ==> getNodeExp e g ~= undefVertex"
apply (simp add:wfExp_def getNodeExp_def, auto)
apply (case_tac e, auto)
apply (simp add:pathInGraph_def)
apply (simp add:getNodeVal_def)+
done

text{*addVar, add a new edge labeled by the variable, referring to an existing vertex in graph.
     *}

definition addVar:: "label => vertex => graph => graph" where
"addVar l v g ==
  case (getSnodeList g) of [] => g
  | a#p => ((% vp. % lp. (if (vp = (R a) & lp = l & (v ~= undefVertex)) then v else  ((getEdgeFun g) vp lp))), 
  getOnodeFun g, getVnodeFun g, getSnodeList g)"

definition addVarG:: "label => exp => graph => graph" where
"addVarG l v g == addVar l (getNodeExp v g) g"

definition Var:: "label => exp => graph => graph" where
"Var l v g == if (getNodeExp v g ~= undefVertex) then addVarG l v (createSnode g) else g"

(* Sometimes we need to add multiple variables at one time. Note: only override ones with defined values!*)
definition addVarList:: " labelVerF => graph => graph" where
"addVarList f g ==
  case (getSnodeList g) of [] => g
  | a#p => ((% vp. % lp. (if (vp = (R a) & (EX v. v ~= undefVertex & f lp = v)) then (f lp) else  ((getEdgeFun g) vp lp))), 
  snd g)"

definition addVarsG:: "labelExpF => graph => graph" where
"addVarsG f g == addVarList (expToNode f g) g"

lemma addVarsGNotChangeOnodefun: "getOnodeFun (addVarsG f g) = getOnodeFun g"
apply (simp add:addVarsG_def addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarsGNotChangeVnodefun: "getVnodeFun (addVarsG f g) = getVnodeFun g"
apply (simp add:addVarsG_def addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarsGNotChangeSnodeList: "getSnodeList (addVarsG f g) = getSnodeList g"
apply (simp add:addVarsG_def addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarsGPreservesEdgesFromNonSnode: "~ (n = R (hd (getSnodeList g))) ==> 
                                    (getEdgeFun (addVarsG f g)) n l = (getEdgeFun g) n l"
apply (simp add:addVarsG_def addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

  (*wflabelExpF is required when invoking this method!! *)
definition Vars:: "labelExpF => graph => graph" where
"Vars f g == addVarsG f (createSnode g)"

(* We are giving the wfness of addVar and addVarList by a set of lemmas and the main theorem wfaddVar in the following. *)
lemma addVarNotChangeSnodeList: "getSnodeList (addVar l v g) = getSnodeList g" 
apply (simp add:addVar_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarListNotChangeSnodeList: "getSnodeList (addVarList l g) = getSnodeList g" 
apply (simp add:addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarPreservesisUnique: "isCorrectSnode g ==> isUnique (getSnodeList (addVar l v g))"
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarNotChangeSnodeList)
apply (simp add:isCorrectSnode_def)
done

lemma addVarListPreservesisUnique: "isCorrectSnode g ==> isUnique (getSnodeList (addVarList l g))"
apply (cut_tac g = "g" and l = "l" in addVarListNotChangeSnodeList)
apply (simp add:isCorrectSnode_def)
done

lemma addVarPreservesGetEdgeFun: " isInVertex (getEdgeFun g) x m ==> isInVertex (getEdgeFun (addVar l v g)) x m"
apply (simp add: isInVertex_def addVar_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarListPreservesGetEdgeFun: "isInVertex (getEdgeFun g) x m ==>
                                      isInVertex (getEdgeFun (addVarList l g)) x m"
apply (simp add: isInVertex_def addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarPreservesGetEdgeFunR: "ALL r. v ~= R r ==> (getEdgeFun g) x m ~= R t ==> 
                                 (getEdgeFun (addVar l v g)) x m ~= R t"
apply (simp add:addVar_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarListPreservesGetEdgeFunR: "ALL v r. l v ~= R r ==> (getEdgeFun g) x m ~= R t ==> 
                                       (getEdgeFun (addVarList l g)) x m ~= R t"
apply (simp add:addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarPreservessnodesAreSources: "isCorrectSnode g ==> snodesAreSources (addVar l v g)"
apply (simp add:isCorrectSnode_def snodesAreSources_def, auto)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarNotChangeSnodeList, auto)
apply (drule spec mp, auto)
apply (cut_tac v = "v" and g = "g" and l = "l" and x = "R r" and m = "la" in addVarPreservesGetEdgeFun, auto)
apply (simp add:isInVertex_def)+
apply (rule exI, auto)
done

lemma addVarListPreservessnodesAreSources: "isCorrectSnode g ==> snodesAreSources (addVarList l g)"
apply (simp add:isCorrectSnode_def snodesAreSources_def, auto)
apply (cut_tac g = "g" and l = "l" in addVarListNotChangeSnodeList, auto)
apply (drule spec mp, auto)
apply (cut_tac g = "g" and l = "l" and x = "R r" and m = "la" in addVarListPreservesGetEdgeFun, auto)
apply (simp add:isInVertex_def)+
apply (rule exI, auto)
done

lemma addVarPreservesisNotTargetList: "ALL x. v ~= R x ==> isNotTargetList g ==>
                                       isNotTargetList (addVar l v g)"
apply (simp add:isNotTargetList_def, auto)
apply (cut_tac v = "v" and g = "g" and x = "x" and m = "la" and t = "y" in addVarPreservesGetEdgeFunR, auto)
done

lemma addVarListPreservesisNotTargetList: "ALL v r. l v ~= R r ==> isNotTargetList g ==>
                                           isNotTargetList (addVarList l g)"
apply (simp add:isNotTargetList_def, auto)
apply (cut_tac g = "g" and x = "x" and m = "la" and t = "y" in addVarListPreservesGetEdgeFunR, auto)
done

lemma addVarPreservessnodesAreDefined: "isCorrectSnode g ==> snodesAreDefined (getSnodeList (addVar l v g))"
apply (simp add: isCorrectSnode_def)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarNotChangeSnodeList, auto)
done

lemma addVarListPreservessnodesAreDefined: "isCorrectSnode g ==> snodesAreDefined (getSnodeList (addVarList l g))"
apply (simp add: isCorrectSnode_def)
apply (cut_tac g = "g" and l = "l" in addVarListNotChangeSnodeList, auto)
done

lemma addVarPreservesisGoodFunction: "wfGraph g ==> isGoodFunction (addVar l v g)"
apply (simp add: wfGraph_def isGoodFunction_def addVar_def, auto)
apply (case_tac "snd (snd (snd g))", auto)
apply (simp add: addVar_def isCorrectSnode_def snodesAreDefined_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarListPreservesisGoodFunction: "wfGraph g ==> isGoodFunction (addVarList l g)"
apply (simp add: wfGraph_def isGoodFunction_def addVarList_def, auto)
apply (case_tac "snd (snd (snd g))", auto)
apply (simp add: addVarList_def isCorrectSnode_def snodesAreDefined_def)
apply (case_tac "snd (snd (snd g))", auto)
done

lemma addVarListPreservesisGoodFunction_1: "snodesAreDefined (getSnodeList g) ==>
                                            isGoodFunction g ==> isGoodFunction (addVarList l g)"
apply (simp add: isGoodFunction_def addVarList_def, auto)
apply (case_tac "snd (snd (snd g))", auto)
apply (simp add: addVarList_def snodesAreDefined_def)
apply (case_tac "snd (snd (snd g))", auto)
done

theorem wfaddVar: "ALL x. v ~= R x ==> wfGraph g ==> wfGraph (addVar l v g)"
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarPreservesisGoodFunction, auto)
apply (simp add:wfGraph_def)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarPreservesisUnique, simp)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarPreservessnodesAreSources, simp)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarPreservesisNotTargetList, auto)
apply (simp add:isCorrectSnode_def)
apply (cut_tac g = "g" and l = "l" and v = "v" in addVarPreservessnodesAreDefined, auto)
apply (simp add:isCorrectSnode_def)
done

theorem wfaddVarList: "ALL v r. l v ~= R r ==> wfGraph g ==> wfGraph (addVarList l g)"
apply (cut_tac g = "g" and l = "l" in addVarListPreservesisGoodFunction, auto)
apply (simp add:wfGraph_def)
apply (cut_tac g = "g" and l = "l" in addVarListPreservesisUnique, simp)
apply (cut_tac g = "g" and l = "l" in addVarListPreservessnodesAreSources, simp)
apply (cut_tac g = "g" and l = "l" in addVarListPreservesisNotTargetList, auto)
apply (simp add:isCorrectSnode_def)
apply (cut_tac g = "g" and l = "l" in addVarListPreservessnodesAreDefined, auto)
apply (simp add:isCorrectSnode_def)
done

lemma createSnodePreservesSnodesAD: "snodesAreDefined (getSnodeList g) ==> snodesAreDefined (getSnodeList (createSnode g))"
apply (simp add:snodesAreDefined_def createSnode_def, auto)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec, auto)
done

lemma createSnodePreservesisGF: "isGoodFunction g ==> isGoodFunction (createSnode g)"
apply (simp add:isGoodFunction_def)
apply (cut_tac g = "g" in createSnodeNotChangeEdgefun, auto)
done

lemma VarsPreservesisGF: "wfGraph g ==> isGoodFunction (Vars l g)"
apply (simp add:Vars_def addVarsG_def wfGraph_def isCorrectSnode_def)
apply (cut_tac g = "g" in createSnodePreservesSnodesAD, auto)
apply (cut_tac g = "g" in createSnodePreservesisGF, auto)
apply (cut_tac g = "createSnode g" and l = "expToNode l (createSnode g)" in addVarListPreservesisGoodFunction_1, auto)
done

lemma VarsPreservessnodesAD: "wfGraph g ==> snodesAreDefined (getSnodeList (Vars l g))"
apply (simp add:Vars_def addVarsG_def wfGraph_def isCorrectSnode_def)
apply (cut_tac g = "g" in createSnodePreservesSnodesAD, auto)
apply (cut_tac g = "createSnode g" and l = "expToNode l (createSnode g)" in addVarListNotChangeSnodeList, auto)
done

lemma createSnodePreservesisU: "wfGraph g ==>isUnique (getSnodeList (createSnode g))"
apply (simp add:wfGraph_def isCorrectSnode_def, auto)
apply (simp add:createSnode_def, auto)
apply (cut_tac g = "g" in getFreshSnodeIsUnique_spec, auto)
apply (simp add:vertexNotInGraph_def vertexNotInEdges_def snodesAreSources_def, auto)
done

lemma VarsPreservesisU: "wfGraph g ==>isUnique (getSnodeList (Vars l g))"
apply (simp add:Vars_def addVarsG_def)
apply (cut_tac g = "g" in createSnodePreservesisU, auto)
apply (cut_tac g = "createSnode g" and l = "expToNode l (createSnode g)" in addVarListNotChangeSnodeList, auto)
done

lemma createSnodeNotChangeGetIntExp: "getIntOfExp e g = getIntOfExp e (createSnode g)"
apply (induct e, auto)
apply (simp add:getIntOfPath_def getInt_def)
apply (cut_tac g = "g" and p = "list" in createSnodeNotChangeGetVertexP, auto)
apply (cut_tac g = "g" in createSnodeNotChangeVnodefun, auto)
apply (case_tac "getVertexPath list (createSnode g)", auto)
done

lemma expFactE: "expToNode l g v = (expToNode l (createSnode g)) v "
apply (simp add:expToNode_def)
apply (simp add:getNodeExp_def)
apply (cut_tac g = "g" and e = "l v" in createSnodeNotChangeGetIntExp)
apply (case_tac "l v", auto)
apply (cut_tac g = "g" and p = "list" in createSnodeNotChangeGetVertexP, auto)
done

lemma createSnodePreservesisNTL: "wfGraph g ==> isNotTargetList (createSnode g)"
apply (simp add:wfGraph_def isCorrectSnode_def isNotTargetList_def, auto)
apply (cut_tac g = "g" in createSnodeNotChangeEdgefun, auto)
done

lemma wflabelExpFImplyNotR: "wfGraph g ==> wflabelExpF l g ==> ALL v r. expToNode l g v ~= R r"
apply (simp add:wflabelExpF_def expToNode_def getNodeExp_def, auto)
apply (subgoal_tac "l v = undefExp | wfExp (l v) g ")
prefer 2
apply (drule spec mp)
apply assumption
apply (case_tac "l v", auto)
apply (simp add:wfExp_def)
apply (cut_tac p = "list" and g = "g" in pathInGraphImpliesNotSnodeNode, auto)
apply (simp add:getNodeVal_def)+
done

lemma VarsPreservesisNTL: " wflabelExpF l g ==> wfGraph g ==> isNotTargetList (Vars l g)"
apply (simp add:Vars_def addVarsG_def)
apply (cut_tac l = "expToNode l (createSnode g)" and g = "createSnode g" in addVarListPreservesisNotTargetList, auto)
apply (cut_tac l = "l" and g = "g" and v = "v" in expFactE, auto)
apply (cut_tac l = "l" and g = "g" in wflabelExpFImplyNotR, auto)
apply (cut_tac g = "g" in createSnodePreservesisNTL, auto)
done

lemma wflabelExpFImplyExNotUndef: "wflabelExpF l g ==> EX v. expToNode l g v ~= undefVertex"
apply (simp add:wflabelExpF_def, auto)
apply (subgoal_tac "l la = undefExp | wfExp (l la) g ")
prefer 2
apply (drule spec mp)
apply assumption
apply simp
apply (subgoal_tac "expToNode l g la ~= undefVertex", auto)
apply (simp add:expToNode_def)
apply (cut_tac e = "l la" and g = "g" in wfExpIsNotUndef, auto)
done

lemma VarsPreservessnodesAS: "wflabelExpF l g ==> wfGraph g ==>  snodesAreSources (Vars l g)"
apply (cut_tac l = "l" and g = "g" in wflabelExpFImplyExNotUndef, auto)
apply (simp add:Vars_def addVarsG_def addVarList_def snodesAreSources_def, auto)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (case_tac "snd (snd (snd (createSnode g)))", simp)
apply (case_tac "r = a", simp)
apply (cut_tac g = "g" and l = "l" and v = "v" in expFactE, auto)
apply (subgoal_tac "r mem snd (snd (snd g))")
apply (simp add:wfGraph_def isCorrectSnode_def snodesAreSources_def, auto)
apply (drule spec mp, auto)
apply (cut_tac g = "g" in createSnodeNotChangeEdgefun, auto)
apply (simp add:createSnode_def)
done

theorem wfVars: "wflabelExpF l g ==> wfGraph g ==> wfGraph (Vars l g)"
apply (cut_tac g = "g" and l = "l" in VarsPreservesisU, auto)
apply (cut_tac g = "g" and l = "l" in VarsPreservessnodesAD, auto)
apply (cut_tac g = "g" and l = "l" in VarsPreservesisGF, auto)
apply (cut_tac g = "g" and l = "l" in VarsPreservesisNTL, auto)
apply (cut_tac g = "g" and l = "l" in VarsPreservessnodesAS, auto)
apply (simp add:wfGraph_def isCorrectSnode_def)
done

(* The theorem says that the new added variable gets correct value *)
theorem addVarGetValue: "getSnodeList g ~= [] ==> v ~= undefVertex
                        ==>  getVertexPath [l] (addVar l v g) = v"
apply (simp add:addVar_def)
apply (case_tac "snd (snd (snd g))", auto)
apply (simp add:getVertexPath_def, auto)
apply (simp add:getSnodeOfVar_def)
apply (simp add:isInVertex_def)
done

theorem addVarListGetValues: "getSnodeList g ~= [] ==> l v ~= undefVertex
                        ==>  getVertexPath [v] (addVarList l g) = l v"
apply (simp add:addVarList_def)
apply (case_tac "snd (snd (snd g))", auto)
apply (simp add:getVertexPath_def, auto)
apply (simp add:getSnodeOfVar_def)
apply (simp add:isInVertex_def)
done

theorem addVarGetValue_Int: "wfGraph g ==> getSnodeList g ~= []  
                              ==>  getIntOfPath [l] (addVar l (getNodeVal (Zint n)) g) = n"
apply (simp add:getIntOfPath_def getInt_def)
apply (cut_tac l = "l" and v = "getNodeVal (Zint n)" and g = "g" in addVarGetValue, auto)
apply (simp add:getNodeVal_def)+
apply (cut_tac g = "(addVar l (L (getVnodeFromVal (val.Zint n))) g)"
                and n = "val.Zint n" in getVnodeFromVal_spec, auto)
done  

(* consts getAttrsOfCtype:: "ctype => labelValF" *)
consts getAttrsOfCtype:: "ctype => labelExpF"

definition addAttrs:: "vertex => labelVerF => graph => graph" where
"addAttrs m p g == ((% vp. % lp. (if (vp = m & (EX v. v ~= undefVertex & p lp = v)) then (p lp) 
                                 else  ((getEdgeFun g) vp lp))), snd g)"

definition addObject:: "path => ctype => graph => graph" where
"addObject l s g == let v = (N (getNodeFromType s g)) in addAttrs v (expToNode (getAttrsOfCtype s) g) (swingPath l v g)" 

(* Properties of addObject *)

lemma addAttrsNotChangeSnodeList: "getSnodeList g = getSnodeList (addAttrs v p g)"
apply (simp add:addAttrs_def)
done 

lemma addAttrsNotChangeIsInVertex: 
"v ~= b ==> (isInVertex (fst (addAttrs v p g)) b a = isInVertex (fst g) b a)"
apply (simp add:isInVertex_def addAttrs_def)
done

(* For the following two lemmas, we change the condition NodeNotInGraph to be NodeNewInGraph, weaker than *)
(* the previous one, for the reason that g will be swingPath g l v, where v is already in g. But at the same time, *)
(* we need more conditions to ensure the lemmas hold, e.g, PathInGraph, .. *)

lemma factForNv: "NodeNotInGraph v g ==> getOwner p g ~= N v"
apply (simp add:NodeNotInGraph_def NodeNotInEdges_def)
apply (induct p, auto)
done

lemma factForNv1: "NodeNewInGraph v g ==> pathInGraph p g ==> getOwner p g ~= N v"
apply (simp add:NodeNewInGraph_def NodeNotHasOutEdges_def pathInGraph_def, auto)
apply (subgoal_tac "p ~= []", auto)
apply (cut_tac p = "p" and g = "g" in gVPisAfterOwner, auto)
done

lemma addAttrsNotChangeOwner: "l ~=[] ==> NodeNotInGraph v g ==>
                                getOwner l (addAttrs (N v) p g) = getOwner l g"
apply (induct l, auto)
apply (simp add:getSnodeOfVar_def)
apply (subgoal_tac " getSnodeOfVarEL (fst (addAttrs (N v) p g)) a (snd (snd (snd g))) =
                     getSnodeOfVarEL (fst g) a (snd (snd (snd g)))")
prefer 2
apply (induct "snd (snd (snd g))", auto)
apply (subgoal_tac "R a ~= N v")
apply (cut_tac v = "N v" and b = "R a" and g = "g" and p = "p" and a = "aa" in addAttrsNotChangeIsInVertex, auto)
apply (subgoal_tac "R a ~= N v")
apply (cut_tac v = "N v" and b = "R a" and g = "g" and p = "p" and a = "aa" in addAttrsNotChangeIsInVertex, auto)
apply (cut_tac v = "N v" and p = "p" and g = "g" in addAttrsNotChangeSnodeList, auto)
apply (simp add:addAttrs_def, auto)
apply (cut_tac g = "g" and v = "v" and p = "l" in factForNv, auto)
done

lemma addAttrsNotChangeOwner1: "wfGraph g ==> NodeNewInGraph v g ==> pathInGraph l g ==>
                                getOwner l (addAttrs (N v) p g) = getOwner l g"
apply (induct l, auto)
apply (simp add:getSnodeOfVar_def)
apply (subgoal_tac " getSnodeOfVarEL (fst (addAttrs (N v) p g)) a (snd (snd (snd g))) =
                     getSnodeOfVarEL (fst g) a (snd (snd (snd g)))")
prefer 2
apply (induct "snd (snd (snd g))", auto)
apply (subgoal_tac "R a ~= N v")
apply (cut_tac v = "N v" and b = "R a" and g = "g" and p = "p" and a = "aa" in addAttrsNotChangeIsInVertex, auto)
apply (subgoal_tac "R a ~= N v")
apply (cut_tac v = "N v" and b = "R a" and g = "g" and p = "p" and a = "aa" in addAttrsNotChangeIsInVertex, auto)
apply (cut_tac v = "N v" and p = "p" and g = "g" in addAttrsNotChangeSnodeList, auto)
apply (subgoal_tac "pathInGraph l g")
prefer 2
apply (simp add:pathInGraph_def, auto)
apply (cut_tac g = "g" and a = "a" and p = "l" in gVPisNext, auto)
apply (simp add:wfGraph_def isGoodFunction_def)
apply (simp add:addAttrs_def, auto)
apply (cut_tac g = "g" and v = "v" and p = "l" in factForNv1, auto)
done

lemma addAttrsNotChangeVertexOfPath: "l ~=[] ==> NodeNotInGraph v g ==>
                                getVertexPath l (addAttrs (N v) p g) = getVertexPath l g"
apply (simp add:getVertexPath_def)
apply (cut_tac l = "l" and g = "g" and v = "v" and p = "p" in addAttrsNotChangeOwner, auto)
apply (simp add:addAttrs_def, auto)
apply (cut_tac g = "g" and v = "v" and p = "l" in factForNv, auto)
done

lemma addAttrsNotChangeVertexOfPath1: "wfGraph g  ==> NodeNewInGraph v g ==> pathInGraph l g ==>
                                       getVertexPath l (addAttrs (N v) p g)
                                     = getVertexPath l g"
apply (simp add:getVertexPath_def)
apply (cut_tac l = "l" and g = "g" and v = "v" and p = "p" in addAttrsNotChangeOwner1, auto)
apply (simp add:addAttrs_def, auto)
apply (cut_tac g = "g" and v = "v" and p = "l" in factForNv1, auto)
done

lemma swingPathPreservesNodeNewIG: " NodeNewInGraph (getNodeFromType s g) (swingPath l (N (getNodeFromType s g)) g)"
apply (simp add:NodeNewInGraph_def NodeNotHasOutEdges_def, auto)		
apply (cut_tac g = "g" and c = "s" in getNodeFromType_spec, auto)
apply (simp add:Let_def NodeNotInGraph_def NodeNotInEdges_def, auto)
apply (simp add:swingPath_def swingEdge_def, auto)
done

lemma swingPathPreservesPathInGraph: "wfGraph g ==> wfPath l g ==>
                                      pathInGraph l (swingPath l (N (getNodeFromType s g)) g)"
apply (simp add:pathInGraph_def, auto)
apply (cut_tac g = "g" and c = "s" in getNodeFromTypeIsNotUndef)
apply (cut_tac g = "g" and p = "l" and n = "N (getNodeFromType s g)" in swingPathChangeVertex, auto)
done

lemma addObjectReferToNewN: "wfGraph g ==> wfPath l g ==> getVertexPath l (addObject l s g) = N (getNodeFromType s g)"
apply (simp add:addObject_def Let_def)
apply (subgoal_tac "wfGraph (swingPath l (N (getNodeFromType s g)) g)" )
apply (subgoal_tac "NodeNewInGraph (getNodeFromType s g) (swingPath l (N (getNodeFromType s g)) g)")
apply (subgoal_tac "pathInGraph l (swingPath l (N (getNodeFromType s g)) g)")
apply (cut_tac g = "swingPath l (N (getNodeFromType s g)) g" and v = "getNodeFromType s g"
               and l = "l" and p = "(expToNode (getAttrsOfCtype s) g)" in addAttrsNotChangeVertexOfPath1, auto)
apply (cut_tac g = "g" and p = "l" and n = "N (getNodeFromType s g)" in swingPathChangeVertex, auto)
apply (simp add:swingPathPreservesPathInGraph)
apply (simp add:wfPath_def)
apply (simp add:swingPathPreservesNodeNewIG)
apply (cut_tac n = "N (getNodeFromType s g)" and g = "g" and p = "l" in wfswingPath, auto)
done

lemma addObjectNotChangeSnodeList: "getSnodeList (addObject l s g) = getSnodeList g"
apply (simp add:addObject_def Let_def)
apply (cut_tac g = "swingPath l (N (getNodeFromType s g)) g" and v = "N (getNodeFromType s g)" and
               p = "expToNode (getAttrsOfCtype s) g" in addAttrsNotChangeSnodeList, auto)
apply (cut_tac g = "g" and p = "l" and n = "N (getNodeFromType s g)" in swingPathNotChangeSnodeList, auto)
done 

lemma addObjectPreservesisUnique: "isUnique (getSnodeList g) ==> isUnique(getSnodeList (addObject l s g))"
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectNotChangeSnodeList, auto)
done 

lemma addObjectPreservesEdgefun: "isInVertex (getEdgeFun g) n x ==> isInVertex (getEdgeFun (addObject l s g)) n x"
apply (simp add:isInVertex_def addObject_def Let_def addAttrs_def, auto)
apply (cut_tac g = "g" and p = "l" and n = "N (getNodeFromType s g)" and v = "n" and l = "x"
       in swingPathPreservesEdgefun, auto)
apply (simp add:isInVertex_def)+
apply (cut_tac g = "g" and c = "s" in getNodeFromType_spec)
apply (simp add:Let_def NodeNotInGraph_def NodeNotInEdges_def)
apply (cut_tac g = "g" and p = "l" and n = "N (getNodeFromType s g)" and v = "n" and l = "x"
       in swingPathPreservesEdgefun, auto)
apply (simp add:isInVertex_def)+
done

lemma addObjectPreservessnodesAreSources: "snodesAreSources g ==>  snodesAreSources (addObject l s g)"
apply (simp add:snodesAreSources_def, auto)
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectNotChangeSnodeList, auto)
apply (drule spec mp, auto )
apply (cut_tac g = "g" and n = "R r" and x = "la" and l = "l" and s = "s" in addObjectPreservesEdgefun, auto)
apply (simp add:isInVertex_def)+
apply (rule exI, simp)
done

lemma addObjectPreservesisNotTargetList: "wfGraph g ==> wflabelExpF (getAttrsOfCtype s) g 
                                          ==>  isNotTargetList (addObject l s g)"
apply (cut_tac g = "g" and l = "getAttrsOfCtype s" in wflabelExpFImplyNotR, auto)
apply (simp add:isNotTargetList_def addObject_def addAttrs_def Let_def)
apply (rule allI)+
apply (rule impI)+
apply (cut_tac n = "N (getNodeFromType s g)" and g = "g" and p = "l" in swingPathPreservesisNotTargetList, simp)
apply (simp add:wfGraph_def isCorrectSnode_def)
apply (simp add: isNotTargetList_def)
done

lemma addObjectPreservessnodesAreDefined: 
      "snodesAreDefined (getSnodeList g) ==> snodesAreDefined (getSnodeList (addObject l s g))"
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectNotChangeSnodeList, auto)
done

lemma  addObjectPreservesisGoodFunction: "wfGraph g ==> isGoodFunction g  ==> isGoodFunction (addObject l s g)"
apply (simp add:isGoodFunction_def addObject_def addAttrs_def Let_def, auto)
apply (cut_tac g = "g" and g = "g" and p = "l" and n = "N (getNodeFromType s g)" in swingPathPreservesisGoodFunction, auto)
apply (simp add: isGoodFunction_def)
apply (cut_tac g = "g" and g = "g" and p = "l" and n = "N (getNodeFromType s g)" in swingPathPreservesisGoodFunction, auto)
apply (simp add: isGoodFunction_def)
done

theorem wfaddObject: "wflabelExpF (getAttrsOfCtype s) g ==> wfGraph g ==> wfGraph (addObject l s g)"
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectPreservesisNotTargetList, auto)
apply (simp add:wfGraph_def isCorrectSnode_def)
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectPreservesisUnique, auto)
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectPreservessnodesAreSources, auto)
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectPreservessnodesAreDefined, auto)
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectPreservesisGoodFunction, auto)
apply (simp add: wfGraph_def isCorrectSnode_def)
done

theorem newObjectAttrGetsCorrectInitValue : 
"wfGraph g ==> wfPath l g ==> (expToNode (getAttrsOfCtype s) g) x ~= undefVertex 
           ==> getVertexPath (x#l) (addObject l s g) = (expToNode (getAttrsOfCtype s) g) x"
apply (cut_tac g = "g" and l = "l" and s = "s" in addObjectReferToNewN, auto)
apply (simp add:addObject_def)
apply (simp add:wfPath_def Let_def)
apply (cut_tac g = "g" and p = "l" in pathInGraphImpliesNotEmpty, auto)
apply (cut_tac p = "l" and 
       g = "addAttrs (N (getNodeFromType s g)) (expToNode (getAttrsOfCtype s) g) (swingPath l (N (getNodeFromType s g)) g)" 
       and a = "x" in gVPisNext, simp)
apply (simp add:addAttrs_def)
done

(*Method Call *)
(* For method call, first we need to get the actual class of the method being called, depending on *)
(* the value of the caller, so called @dynamic binding@. *)
definition getCtype:: "exp => graph => ctype" where
"getCtype e g == case e of (Path p) => 
                    (case (getVertexPath p g) of  N n => (getOnodeFun g) n | _ => undefType)
                          | (Val v) => undefType
                          | undefExp => undefType"

(* Signature of Method*)
consts getValueType:: "ctype => mname => ctype list" 

consts getReturnType:: "ctype => mname => ctype"

types
pair = "(label *  exp) list"

consts getLabelExpF:: "pair => labelExpF" 
primrec
"getLabelExpF [] l = undefExp"
"getLabelExpF (a # p) l = (if (l = (fst a)) then (snd a) else ((getLabelExpF p) l))"

(*****************************Other Properties*************************************)

lemma sameNodefun : "getOnodeFun (swingPath p n g) = 
                     getOnodeFun (removeSnode (swingPath b n (Vars f g)))"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathNotChangeOnodefun, auto)
apply (simp add:Vars_def)
apply (cut_tac g = "g" in createSnodeNotChangeOnodefun, auto)
apply (cut_tac g = "createSnode g" and f = "f"  in addVarsGNotChangeOnodefun, auto)
apply (cut_tac g = "addVarsG f (createSnode g)" and p = "b" and n = "n" 
                 in swingPathNotChangeOnodefun, auto)
apply (cut_tac g = "(swingPath b n (addVarsG f (createSnode g)))" 
                 in removeSnodeNotChangeOnodefun, auto)
done

lemma sameVnodefun : "getVnodeFun (swingPath p n g) =
                     getVnodeFun (removeSnode (swingPath b n (Vars f g)))"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathNotChangeVnodefun, auto)
apply (simp add:Vars_def)
apply (cut_tac g = "g" in createSnodeNotChangeVnodefun, auto)
apply (cut_tac g = "createSnode g" and f = "f" in addVarsGNotChangeVnodefun, auto)
apply (cut_tac g = "addVarsG f (createSnode g)" and p = "b" and n = "n" 
                 in swingPathNotChangeVnodefun, auto)
apply (cut_tac g = "(swingPath b n (addVarsG f (createSnode g)))"
                 in removeSnodeNotChangeVnodefun, auto)
done

lemma sameSnodeList : "getSnodeList (swingPath p n g) =
                      getSnodeList (removeSnode (swingPath b n (Vars f g)))"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathNotChangeSnodeList, auto)
apply (simp add:Vars_def)
apply (cut_tac g = "createSnode g" and f = "f"  in addVarsGNotChangeSnodeList, auto)
apply (cut_tac g = "addVarsG f (createSnode g)" and p = "b" and n = "n" 
                 in swingPathNotChangeSnodeList, auto)
apply (cut_tac g = "g" in removeCreateNotChangeSnodeList, auto)
apply (cut_tac u = "swingPath b n (addVarsG f (createSnode g))" and v = "createSnode g" 
                 in removeSnodePreservesEqualSnodeList, auto)
done

lemma vertexNotChange_1: "f l = Path p ==> (wflabelExpF f g) ==> 
                          getVertexPath p g =
                          getVertexPath [l] (Vars f g)"
apply (simp add:Vars_def addVarsG_def)
apply (cut_tac g = "g" in createSnodeListNotEmpty)
apply (subgoal_tac "expToNode f (createSnode g) l ~= undefVertex")
apply (cut_tac g = "(createSnode g)" and 
               l = "expToNode f (createSnode g)"
           and v = "l" in addVarListGetValues, auto)
apply (simp add:expToNode_def getNodeExp_def)
apply (cut_tac g = "g" and p = "p" in createSnodeNotChangeGetVertexP, auto)
apply (simp add:wflabelExpF_def, auto)
apply (subgoal_tac "f l = undefExp | wfExp (f l) g", simp)
apply (cut_tac e = "f l" and g = "g" in wfExpIsNotUndef, simp)
apply (simp add:expToNode_def getNodeExp_def) 
apply (cut_tac g = "g" and p = "p" in createSnodeNotChangeGetVertexP, simp)
apply (drule spec mp, assumption)
done

(* This lemma can be generalised in the way  that ''a'' be changed to an arbitrary path. TO DO *)
lemma vertexNotChange_2: "p ~= [] ==> f l = Path p ==>(wflabelExpF f g)
                          ==>  getVertexPath (a # p) g = getVertexPath (a # [l]) (Vars f g)"
apply (simp add:Vars_def)
apply (cut_tac p = "p" and g = "g" and a = "a" in gVPisNext, auto)
apply (cut_tac p = "[l]" and g = "addVarsG f (createSnode g)" and a = "a" in gVPisNext, auto)
apply (cut_tac f = "f" and l = "l" and p = "p" and g = "g" in vertexNotChange_1, auto)
apply (simp add:Vars_def)
apply (subgoal_tac "getVertexPath p g ~= R (hd (getSnodeList (createSnode g)))")
apply (cut_tac n = "getVertexPath [l] (addVarsG f (createSnode g))
        " and g = "createSnode g" and f = "f"
           and l = "a" in addVarsGPreservesEdgesFromNonSnode, auto)
apply (cut_tac g = "g" in createSnodeNotChangeEdgefun, auto)
apply (cut_tac g = "g" and p = "p" in getVertexPathIsNotNewSnode, auto)
done

(* Can be generalised as well: ''a'' to any path. *)
lemma ownerNotChange: "p ~= [] ==> f l = Path p ==> (wflabelExpF f g)
                        ==> getOwner (a # p) g = getOwner (a # [l]) (Vars f g)"
apply (cut_tac p = "a#p" and g = "g" in ownerIsgVPprefix, simp)
apply (cut_tac p = "a # [l]" and  g = "(Vars f g)" in ownerIsgVPprefix, simp)
apply (cut_tac f = "f" and l = "l" and p = "p" and g = "g" in vertexNotChange_1, auto)
done

lemma sameSnodeList_1: "let h = createSnode g in (getSnodeList (swingPath p n (addVarsG f h))
                                              = getSnodeList h)"
apply (cut_tac g = "createSnode g" and f = "f" in addVarsGNotChangeSnodeList, auto)
apply (cut_tac g = "addVarsG f (createSnode g)" and p = "p" and n = "n" in swingPathNotChangeSnodeList, auto)
done


lemma getValue_1: "n ~= undefVertex ==> wfPath p g ==> fst (swingPath p n g) (getOwner p g) (hd p) = n"
apply (cut_tac n = "n" and g = "g" and p = "p" in swingPathChangeEdge, auto)
apply (simp add:wfPath_def)
done

lemma getValue_2: "n ~= undefVertex ==> p ~= [] ==> f l = Path p ==> (wflabelExpF f g) ==> wfPath (a # p) g
                   ==> fst (swingPath  (a # [l]) n (Vars f g)) (getOwner (a # p) g) a = n"
apply (cut_tac p = "p" and f = "f" and l = "l" and g = "g" and a = "a" in ownerNotChange, simp)
apply simp
apply simp
apply (cut_tac n = "n" and g = "Vars f g" and p = "[a, l]" in swingPathChangeEdge, auto)
apply (simp add:wfPath_def pathInGraph_def)
apply (cut_tac g = "g" and f = "f" and l = "l" and a = "a" in vertexNotChange_2, auto) 
done

lemma sameValueforRemovedSnode: "pathInGraph p g ==>
       fst (swingPath p n g) (R (hd (getSnodeList (createSnode g)))) s =
       fst (removeSnode (swingPath q n (Vars f g))) (R (hd (getSnodeList (createSnode g)))) s"
apply (cut_tac g = "g" and p = " p" and n = "n" and l = "s" in newSnodeNotInSwungGraph, auto)
apply (simp add:isInVertex_def)
apply (subgoal_tac "(getSnodeList ((swingPath q n (Vars f g)))) =  (snd (snd (snd (createSnode g))))")
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (cut_tac g = "swingPath q n (Vars f g)" and l = "s" in removeSnodeRemoveEdges, auto)
apply (simp add:isInVertex_def)
apply (cut_tac g = "createSnode g" and f = "f" in addVarsGNotChangeSnodeList, auto)
apply (cut_tac g = "Vars f g"  and p = "q" and n = "n" in swingPathNotChangeSnodeList, auto)
apply (simp add:Vars_def)
done

lemma sameEdgefun : " m ~= undefVertex ==> p ~= [] ==> f l = Path p ==> wfGraph g 
                      ==>  wfPath (a # p) g ==>  (wflabelExpF f g)
                      ==> (ALL n s. (getEdgeFun (swingPath (a # p) m g)) n s =
                          (getEdgeFun (removeSnode (swingPath (a # [l]) m (Vars f g)))) n s)"
apply (rule allI)+
apply (simp add:Vars_def)
apply (case_tac "n ~= R ( hd (getSnodeList (swingPath (a # [l]) m (addVarsG f (createSnode g)))))")                      
apply (cut_tac v = "n" and g = "swingPath (a # [l]) m (addVarsG f (createSnode g))" and
               l = "s" in removeSnodePreservesGetEdges, simp)
apply (case_tac "~(n = getOwner (a # p) g) | ~(s = a)")
apply (cut_tac n = "n" and l = "s" and g = "g" and p = "(a # p)" and m = "m" 
       in swingPathPreservesUnswungEdges, simp)
apply (subgoal_tac "~ (n = getOwner  [a, l] (addVarsG f (createSnode g))) | ~ (s = a)")
prefer 2
apply (erule disjE)
apply (cut_tac p = "p" and f = "f" and l = "l" and a = "a" and  g = "g" in ownerNotChange)
apply simp
apply simp
apply simp
apply simp
apply (rule impI)
apply (simp add:Vars_def)
apply simp
apply (cut_tac n = "n" and l = "s" and g = "addVarsG f (createSnode g)" and p = "[a, l]" and m = "m"
               in swingPathPreservesUnswungEdges, simp)
apply (subgoal_tac "n ~= R (hd (getSnodeList (createSnode g)))")
prefer 2
apply (cut_tac g = "createSnode g" and f = "f"
               in addVarsGNotChangeSnodeList, simp)
apply (cut_tac g = "addVarsG f (createSnode g)"
            and p = "[a, l]" and n = "m" in swingPathNotChangeSnodeList)
apply simp
apply (cut_tac n = "n" and g = "createSnode g" and f = "f"
           and l = "s" in addVarsGPreservesEdgesFromNonSnode)
apply simp
apply (cut_tac g = "g" in createSnodeNotChangeEdgefun)
apply auto
apply (cut_tac g = "g" and p = "a # p" and n = "m" in getValue_1, auto)
apply (cut_tac n = "m" and p = "p" and f = "f" and l = "l" and a = "a" and g = "g" in getValue_2, auto)
apply (simp add:Vars_def)
apply (subgoal_tac "hd (snd (snd (snd (swingPath [a, l] m
                    (addVarsG f (createSnode g)))))) = hd (getSnodeList (createSnode g))")
prefer 2
apply (cut_tac g = "createSnode g" and f = "f"
               in addVarsGNotChangeSnodeList)
apply (cut_tac g = "addVarsG f (createSnode g)"
            and p = "[a, l]" and n = "m" in swingPathNotChangeSnodeList, auto)
apply (cut_tac g = "g" and s = "s" and p = "a # p" and n = "m" and 
               q = "[a, l]" and f = "f" in sameValueforRemovedSnode, auto)
apply (simp add:wfPath_def)
apply (simp add:Vars_def)
done

lemma sameGraphs : " m ~= undefVertex ==> p ~= [] ==> f l = Path p ==> wfGraph g ==> wfPath (a # p) g
                    ==> (wflabelExpF f g)==>
                   swingPath (a # p) m g = removeSnode (swingPath (a # [l]) m (Vars f g))"
apply (cut_tac g = "g" and p = "(a # p)" and n = "m"
           and f = "f" and b = "a # [l]" in sameNodefun)
apply (cut_tac g = "g" and p = "(a # p)" and n = "m"
           and f = "f" and b = "a # [l]" in sameVnodefun)
apply (cut_tac g = "g" and p = "(a # p)" and n = "m"
           and f = "f" and b = "a # [l]" in sameSnodeList)
apply (cut_tac g = "g" and m = "m" and p = "p" and f = "f" 
           and l = "l" and a = "a" in sameEdgefun, auto)
apply (subgoal_tac "fst (swingPath (a # p) m g) = fst (removeSnode (swingPath [a, l] m (Vars f g)))")
apply (cut_tac g = "swingPath (a # p) m g" in tupleGraph, auto)
apply (simp add: expand_fun_eq) 
done

lemma wfforPathInGraph: "p ~= [] ==> wfGraph g ==> wfPath (a # p) g ==> pathInGraph p g"
apply (simp add:wfPath_def pathInGraph_def, auto)
apply (cut_tac p = "p" and g = "g" and a = "a" in gVPisNext, auto)
apply (simp add:wfGraph_def isGoodFunction_def)
done

lemma snodeOfVarIsDef: "wflabelExpF f g ==> p ~= [] ==> f l = Path p 
                       ==> wfGraph g ==> wfPath (a # p) g ==> 
                       getSnodeOfVar l (Vars f g) ~= undefSnode"
apply (simp add:Vars_def)
apply (simp add:addVarsG_def, auto)
apply (cut_tac  g = "createSnode g" and l = "expToNode f (createSnode g)"
            and v = "l" in addVarListGetValues, auto)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (simp add:expToNode_def getNodeExp_def)
apply (cut_tac g = "g" and p = "p" in createSnodeNotChangeGetVertexP, auto)
apply (simp add:wfPath_def pathInGraph_def)
apply (cut_tac p = "p" and g = "g" and a = "a" in gVPisNext, auto)
apply (simp add:wfGraph_def isGoodFunction_def)
apply (simp add:getVertexPath_def)
apply (cut_tac g = "g" and l = "f" in wfVars, auto)
apply (simp add:wfGraph_def isGoodFunction_def Vars_def addVarsG_def, auto)
apply (simp add:expToNode_def getNodeExp_def)
apply (cut_tac g = "g" and p = "p" in createSnodeNotChangeGetVertexP)
apply (simp add:wfPath_def pathInGraph_def)
apply (cut_tac p = "p" and g = "g" and a = "a" in gVPisNext, auto)
done

lemma varFromSnode_b: "p ~= [] ==> f l = Path p ==> wfGraph g ==> wfPath (a # p) g ==> 
                      wflabelExpF f g ==> (getSnodeOfVar l (Vars f g)) = hd (getSnodeList (Vars f g))"
apply (simp add:getSnodeOfVar_def Vars_def addVarsG_def)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (subgoal_tac "isInVertex (fst (addVarList (expToNode f (createSnode g))  (createSnode g))) 
                               (R (hd (getSnodeList (addVarList (expToNode f (createSnode g))  (createSnode g))))) l")
apply (cut_tac g = "createSnode g" and l = "expToNode f (createSnode g)" in addVarListNotChangeSnodeList, simp) 
apply (case_tac "(snd (snd (snd (createSnode g))))", auto)
apply (simp add:isInVertex_def addVarList_def)
apply (subgoal_tac "EX v. expToNode f (createSnode g) l = v")
apply (case_tac " snd (snd (snd (createSnode g)))", auto)
apply (simp add:wflabelExpF_def, auto)
apply (subgoal_tac "f l = undefExp | wfExp (f l) g", simp)
apply (cut_tac e = "f l" and g = "g" in wfExpIsNotUndef, simp)
apply (simp add:expToNode_def getNodeExp_def) 
apply (cut_tac g = "g" and p = "p" in createSnodeNotChangeGetVertexP, simp)
apply (drule spec mp, assumption)
done

lemma varFromSnode: "p ~= [] ==> f l = Path p ==> wfGraph g ==> wfPath (a # p) g ==> 
                      wflabelExpF f g ==> (getSnodeOfVar l (Vars f g)) mem (getSnodeList (Vars f g))"
apply (cut_tac p = "p" and f = f and l = l and g = g and a = a in varFromSnode_b, auto)
apply (subgoal_tac "snd (snd (snd (Vars f g))) ~= []")
apply (case_tac "snd (snd (snd (Vars f g)))", auto)
apply (simp add:Vars_def)
apply (cut_tac g = "createSnode g" and f = "f" in addVarsGNotChangeSnodeList, auto)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
done

lemma wfPathforVars: "p ~= [] ==> f l = Path p ==> wfGraph g ==> wfPath (a # p) g ==> 
                      wflabelExpF f g ==> wfPath (a # [l]) (Vars f g)"
apply (cut_tac g = "g" and p = "p" and f = "f" and l = "l" and a = "a" 
               in snodeOfVarIsDef, auto)
apply (cut_tac g = "g" and p = "p" and f = "f" and l = "l" and a = "a" 
               in ownerNotChange, auto)
apply (cut_tac  g = "g" and l = "f" in wfVars, auto)
apply (simp add:wfPath_def isGoodPath_def)
apply (rule conjI)
apply (simp add:wfGraph_def isCorrectSnode_def isNotTargetList_def)
apply (simp add:pathInGraph_def)
apply (cut_tac p = "p" and f = "f" and l = "l" and a = "a" and g = "g" in vertexNotChange_2, auto)
done

lemma wfforSwingPathVars: "ALL x. n ~= R x ==> wflabelExpF f g ==>
                          f l = Path p ==> wfGraph g ==> wfPath (a # p) g ==>
                           wfGraph (swingPath (a # [l]) n (Vars f g))"                          
apply (cut_tac g = "g" and l = "f" in wfVars, auto)
apply (cut_tac g = "Vars f g" 
            and p = "a # [l]"
            and n = "n" in wfswingPath, auto)
done

lemma getCorrectLocalValue: "wfGraph g ==> f l = Val (Zint n) ==> getVertexPath [l] (Vars f g) = getNodeVal (Zint n)"
apply (simp add:Vars_def addVarsG_def)
apply (cut_tac g = "createSnode g" and l = "expToNode f (createSnode g)" and 
               v = "l" in addVarListGetValues, auto)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (simp add:expToNode_def getNodeExp_def getNodeVal_def)
apply (cut_tac g = "g" and n = "val.Zint n" in getVnodeFromVal_spec, auto)
apply (simp add:expToNode_def getNodeExp_def getNodeVal_def)
done

lemma getCorrectLocalValuePath: "wfGraph g ==> pathInGraph p g ==>
                                 f l = Path p ==> getVertexPath [l] (Vars f g) = getVertexPath p g"
apply (simp add:Vars_def addVarsG_def)
apply (cut_tac g = "createSnode g" and l = "expToNode f (createSnode g)" and 
               v = "l" in addVarListGetValues, auto)
apply (cut_tac g = "g" in createSnodeListNotEmpty, auto)
apply (simp add:expToNode_def getNodeExp_def getNodeVal_def pathInGraph_def)
apply (cut_tac g = g and p = p in createSnodeNotChangeGetVertexP, auto)
apply (simp add:expToNode_def getNodeExp_def getNodeVal_def)
apply (cut_tac g = g and p = p in createSnodeNotChangeGetVertexP, auto)
done

lemma swingPathPreservesisGoodPath :
  "n ~= undefVertex ==> wfGraph g ==> wfPath p g ==> isGoodPath p (swingPath p n g)"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesGetOwner, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesSameSnodes)
apply (simp add:wfPath_def isGoodPath_def, auto)
apply (simp add:pathInGraph_def sameSnodes_def)+
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesEquivPrefix)
apply (simp add:wfGraph_def isGoodPath_def)
apply (cut_tac g = "g" and h = "swingPath p n g" and p = "tl (tl p)" in equivPrefixEqualGetListofNodes, auto)
apply (cut_tac g = "g" and h = "swingPath p n g" and a = "hd p" and p = "tl p" in sameSnodesPreserved, auto)
apply (simp add:sameSnodes_def)
apply (cut_tac g = "g" and h = "swingPath p n g" and a = "hd (tl p)" and p = "tl (tl p)" in sameSnodesPreserved, auto)
apply (cut_tac g = "g" and h = "swingPath p n g" and p = "tl (tl p)" in equivPrefixEqualGetListofNodes, auto)
apply (cut_tac g = "g" and h = "swingPath p n g" and a = "hd p" and p = "tl p" in sameSnodesPreserved, auto)
apply (cut_tac g = "g" and h = "swingPath p n g" and a = "hd (tl p)" and p = "tl (tl p)" in sameSnodesPreserved, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesEquivPrefix, auto)
apply (simp add:isGoodPath_def)
done

lemma swingPathPreserveswfPath : 
  "n ~= undefVertex ==> wfGraph g ==> wfPath p g ==> wfPath p (swingPath p n g)"
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathPreservesisGoodPath, auto)
apply (cut_tac g = "g" and p = "p" and n = "n" in swingPathChangeVertex, auto)
apply (simp add:wfPath_def pathInGraph_def)
done

lemma swingPathIntPreserveswfPath : 
  "wfGraph g ==> wfPath p g ==> wfPath p (swingPath p (getNodeVal (Zint n)) g)"
apply (cut_tac g = "g" and p = "p" and n = "getNodeVal (Zint n)" in swingPathPreserveswfPath, auto)
apply (simp add:getNodeVal_def)
done


(*<*) end (*>*)

