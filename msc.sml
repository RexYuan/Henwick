(* use vertex to represent full graph connection and node to represent only
   the vertex name, the names of nodes must be unique *)

type node = string
type relation = (node * node) list
type vertex = {name : node, from : node list, to : node list}

(* given a node list ns and a relation rs,
   returns a vertex list representing the graph *)
fun construct_graph (ns,rs) =
    let
        fun edge_helper (n,rs,froms,tos) =
            case rs of
                [] => (froms,tos)
              | (f,t)::rs' => if f=n
                              then edge_helper (n,rs',froms,t::tos)
                              else if t=n
                                   then edge_helper (n,rs',f::froms,tos)
                                   else edge_helper (n,rs',froms,tos)
        fun main_helper (ns,vs) =
            case ns of
                [] => vs
              | n::ns' => let val (from,to) = edge_helper (n,rs,[],[])
                          in main_helper (ns',{name = n, from = from, to = to}::vs) end
    in
        main_helper (ns,[])
    end

type cut = node list
exception NodeNotInGraph
exception NodeAlreadyInCut

(* given a node n and a cut c in a graph of vertices vs, check if the cut property
   holds after adding n to c : forall e and e' in c, e' < e -> e' in c *)
fun safe_node vs c n =
    let
        fun vertex_helper (vs,n) =
            case vs of
                [] => raise NodeNotInGraph
              | {name=vname,from=froms,to=tos}::vs' => if vname=n
                                                       then {name=vname,from=froms,to=tos}
                                                       else vertex_helper (vs',n)
        val {name=_,from=ns,to=_} = vertex_helper (vs,n)
    in
        if List.exists (fn n' => n'=n) c
        then raise NodeAlreadyInCut
        else List.all (fn n' => List.exists (fn n'' => n''=n') c) ns
    end

(* TODO: use TextIO.openIn and TextIO.inputLine to read in msc_sample.txt *)
