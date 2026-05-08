import Benchmark.List.Random
import Autoinc.SequenceTree
import Benchmark.Utils
import Benchmark.Table

def forceSequence [Sequence β γ] (s : γ) : IO Nat := do
  let mut x := 0
  let t₁ ← IO.monoNanosNow
  for _ in Sequence.toList s do
    x := x + 1
  let t₂ ← IO.monoNanosNow
  return t₂ - t₁

def benchmark [Sequence β γ] (f : α → γ) (input : α) (rep : Nat := 50) : IO Float := do
  let mut total : UInt64 := 0
  for _ in [0:rep] do
    let start ← IO.monoNanosNow
    let result := f input
    let t ← forceSequence result
    let stop ← IO.monoNanosNow
    total := total + (stop - start - t).toUInt64
  return total.toFloat / rep.toFloat

def benchmarkList [Sequence β γ] (f : α → γ) (inputs : List α) (rep : Nat := 50) : IO (List Float) := do
  let mut totals : List Float := []
  for input in inputs do
    let t ← benchmark f input rep
    totals := t :: totals
  return totals.reverse

def inputSize := 10000
def input := List.range inputSize
def changeSize := 5.0 -- %

def at_p (p : Float) (size : Nat) : Nat :=
  p * size.toFloat |>.toUInt64 |>.toNat

def execAll (caption : Option String := none) : IO Unit := do
  let list := Sequence.fromList (γ := List Nat) input
  let tree := Sequence.fromList (γ := SequenceTree Nat) input
  let size := (changeSize / 100.0) * inputSize.toFloat |> (·.toUInt64.toNat)
  let gen ← IO.stdGenRef.get
  let inputs := [
    ("Insertion at the start of the list", randIns (at_p 0 inputSize) (at_p 0.1 inputSize) size gen |>.1),
    ("Insertion in the middle of the list", randIns (at_p 0.45 inputSize) (at_p 0.55 inputSize) size gen |>.1),
    ("Insertion at the end of the list", randIns (at_p 0.8 inputSize) (at_p 0.9 inputSize) size gen |>.1),

    ("Deletion at the start of the list", randDel (at_p 0 inputSize) (at_p 0.1 inputSize) size gen |>.1),
    ("Deletion in the middle of the list", randDel (at_p 0.45 inputSize) (at_p 0.55 inputSize) size gen |>.1),
    ("Deletion at the end of the list", randDel (at_p 0.8 inputSize) (at_p 0.9 inputSize) size gen |>.1),

    ("Update at the start of the list", randUpd (at_p 0 inputSize) (at_p 0.1 inputSize) size gen |>.1),
    ("Update in the middle of the list", randUpd (at_p 0.45 inputSize) (at_p 0.55 inputSize) size gen |>.1),
    ("Update at the end of the list", randUpd (at_p 0.8 inputSize) (at_p 0.9 inputSize) size gen |>.1),
  ]

  let inputNames := inputs.map (·.1)
  let inputValues := inputs.map (·.2)
  let listTimes ← benchmarkList (list ⨁ ·) inputValues
  let treeTimes ← benchmarkList (tree ⨁ ·) inputValues
  let speedups := listTimes.zip treeTimes |>.map (fun (t₁, t₂) => t₁ / t₂)

  let headers := ["Description", "List", "Tree", "Speedup (List → Tree)"]
  let rows :=
    inputNames
    |>.zip (listTimes.map (·.trunc ++ "ns"))
    |>.zip (treeTimes.map (·.trunc ++ "ns"))
    |>.zip (speedups.map (·.trunc))
    |>.map (fun (((n, l), t), s) => [n, l, t, s])

  printTable headers rows (caption := caption)
