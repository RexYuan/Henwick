use "msc.sml";

val nodes = ["s1","r1","s2","r2","s3","r3"]
val rels = [("r1","s2"),
            ("r1","s3"),
            ("s1","r1"),
            ("s1","r3"),
            ("s2","r2"),
            ("s2","s3"),
            ("s3","r3")]
val vs = construct_graph (nodes,rels)
val cut1 = ["s1","r1","s2"]
val test1 = safe_node vs cut1 "r2" = true
val test2 = safe_node vs cut1 "s3" = true
val test3 = safe_node vs cut1 "r3" = false
val test4 = safe_node vs cut1 "s2" handle NodeAlreadyInCut => true
val test5 = safe_node vs cut1 "s4" handle NodeNotInGraph => true
val cut2 = ["s1","r1","s2","s3"]
val test6 = safe_node vs cut2 "r2" = true
val test7 = safe_node vs cut2 "r3" = true
val test8 = safe_node vs cut2 "s2" handle NodeAlreadyInCut => true
val test9 = safe_node vs cut2 "s3" handle NodeAlreadyInCut => true
val test10 = safe_node vs cut2 "s4" handle NodeNotInGraph => true
