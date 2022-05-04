open Printf
open Phases

module NeighborSet = Set.Make (String)

type neighborst = NeighborSet.t

module Graph = Map.Make (String)

type grapht = neighborst Graph.t


(* represents a mapping between variable nodes and their degrees, such that we don't *)
(* need to remove the nodes from the graph in the coloring, but we just decrease *)
(* their degrees in the map *)
type grapht_deg = int HashMap.t

module StringSet = Set.Make (String)

(* type livet = StringSet.t *)

let empty : grapht = Graph.empty

let merge (g1 : grapht) (g2 : grapht) : grapht =
  Graph.union (fun _ n1 n2 -> Some (StringSet.union n1 n2)) g1 g2

let add_node (g : grapht) (name : string) : grapht =
  if Graph.mem name g then g else Graph.add name NeighborSet.empty g

let add_directed_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_node (add_node g n1) n2 in
  let curr_neighbors = Graph.find n1 g' in
  Graph.add n1 (NeighborSet.add n2 curr_neighbors) g'

let add_edge (g : grapht) (n1 : string) (n2 : string) : grapht =
  let g' = add_directed_edge g n1 n2 in
  add_directed_edge g' n2 n1

let get_neighbors (g : grapht) (name : string) : string list =
  if Graph.mem name g then NeighborSet.fold (fun n ns -> n :: ns) (Graph.find name g) [] else []

let get_vertices (g : grapht) : string list =
  let keys, _ = List.split (Graph.bindings g) in
  keys

let string_of_graph (g : grapht) : string =
  let string_of_neighbors (n : string) : string = ExtString.String.join ", " (get_neighbors g n) in
  ExtString.String.join "\n"
    (List.map (fun k -> sprintf "%s: %s" k (string_of_neighbors k)) (get_vertices g))

let pairup (g : grapht) (ns : StringSet.t) : grapht =
  let rec edge_up (names : string list) (acc : grapht) : grapht =
    match names with
    | [] -> acc
    | name :: rest ->
        edge_up rest
          (List.fold_left (fun prev_graph n_name -> add_edge prev_graph name n_name) acc rest)
  in
  let ns = StringSet.elements ns in
  let g' = List.fold_left (fun prev_g n -> add_node prev_g n) g ns in
  edge_up ns g'

(* Produces a dotgraph representation of the given graph *)
let graph_to_dotgraph (g : grapht) : string =
  let nodes = get_vertices g in
  let prelude, postlude = ("graph {\n", "}") in
  let nodes_str = String.concat "" (List.map (fun name -> Printf.sprintf "  %s\n" name) nodes) in
  let edges_str =
    String.concat ""
      (List.map
         (fun name ->
           String.concat ""
             (List.map (fun n -> Printf.sprintf "  %s -- %s\n" name n) (get_neighbors g name)) )
         nodes )
  in
  prelude ^ nodes_str ^ edges_str ^ postlude

let get_degree (g : grapht) : grapht_deg =
  HashMap.map (fun nodes -> List.length (StringSet.elements nodes)) g
