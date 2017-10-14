Require Import Arith.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.FOLPredicate.
Require Import PipeGraph.GraphvizCompressed.

Inductive ScenarioTree : Set :=
| ScenarioName : string -> ScenarioTree -> ScenarioTree
| ScenarioAxiomName : string -> ScenarioTree -> ScenarioTree
| ScenarioAnd : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioOr : ScenarioTree -> ScenarioTree -> ScenarioTree
| ScenarioEdgeLeaf : list GraphEdge -> ScenarioTree
| ScenarioNotEdgeLeaf : list GraphEdge -> ScenarioTree
| ScenarioNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioNotNodeLeaf : list GraphNode -> ScenarioTree
| ScenarioLoadConstraint : Microop -> Data -> bool -> ScenarioTree
| ScenarioTrue : ScenarioTree
| ScenarioFalse : ScenarioTree.

