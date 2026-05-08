import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Autoinc.Data.List.Operator
import Benchmark.Experiment
import Benchmark.List.Random
import AssertCmd
open Experiment
namespace Example11

open StructProd3

namespace Benchmark

abbrev A := (List Nat) × Nat
abbrev B := Nat
abbrev ΔA := ΔProd (ΔList Nat ΔNat) ΔNat
abbrev ΔB := List ΔNat

abbrev γ₁ := List Nat
abbrev Env₁ := LazyEagerState γ₁ (Nat × Nat)
-- TODO: is this the correct type and if so, why? I just satisfied the type checker but have no idea why this works
def op₁ : Operator A B ΔA ΔB (StateT Env₁ IO) := ΔList.Count.op (LazyEagerStateT γ₁ (Nat × Nat) _) (α := Nat) (Δα := ΔNat) (γ := γ₁)

abbrev γ₂ := Tree Nat
abbrev Env₂ := LazyEagerState γ₂ (Nat × Nat)
def op₂ : Operator A B ΔA ΔB (StateT Env₂ IO) := ΔList.Count.op (LazyEagerStateT γ₂ (Nat × Nat) _) (α := Nat) (Δα := ΔNat) (γ := γ₂)

abbrev inputSize := 9000
abbrev input₁ := List.range inputSize
abbrev input₂ := inputSize / 3
abbrev input := (input₁, input₂)

instance : SizeOf A where
  sizeOf _ := inputSize

def buildCase₁ (id : Nat) (description : String) (genChange : StdGen → Nat → ΔA) (rep:Nat:=100) : Case A B ΔA ΔB Env₁ where
  op := op₁
  id := id
  description := description
  rep := rep
  input := input
  p := 5
  genChange := genChange

def buildCase₂ (id : Nat) (description : String) (genChange : StdGen → Nat → ΔA) (rep:Nat:=100) : Case A B ΔA ΔB Env₂ where
  op := op₂
  id := id
  description := description
  rep := rep
  input := input
  p := 5
  genChange := genChange

def buildCases (id : Nat) (description : String) (genChange : StdGen → Nat → ΔA) (rep:Nat:=100) :=
  let case₁ := buildCase₁ id description genChange rep
  let case₂ := buildCase₂ id description genChange rep
  (case₁, case₂)

/-
Optimal case:
- Only inserts (no need to update internal list representation)
-/

def case_1 :=
  buildCases
    1
    "insert elements in the first part of the list"
    (fun g size => randIns 1 1000 size g |>.1 |> ΔProd._1)

def case_2 :=
  buildCases
    2
    "insert elements in the middle part of the list"
    (fun g size => randIns 4000 5000 size g |>.1 |> ΔProd._1)

def case_3 :=
  buildCases
    3
    "insert elements in the last part of the list"
    (fun g size => randIns 8000 9000 size g |>.1 |> ΔProd._1)


def case_4 :=
  buildCases
    4
    "delete elements in the first part of the list"
    (fun g size => randDel 1 1000 size g |>.1 |> ΔProd._1)

def case_5 :=
  buildCases
    5
    "delete elements in the middle part of the list"
    (fun g size => randDel 4000 5000 size g |>.1 |> ΔProd._1)

def case_6 :=
  buildCases
    6
    "delete elements in the last part of the list"
    (fun g size => randDel 8000 9000 size g |>.1 |> ΔProd._1)


def cases :=
  [
    case_1,
    case_2,
    case_3,
    case_4,
    case_5,
    case_6,
    -- case_7,
    -- case_8,
    -- case_9,
    -- case_10,
    -- case_11,
    -- case_12
  ]

def cases₁ := cases.map (·.1)
def cases₂ := cases.map (·.2)


end Benchmark





end Example11
