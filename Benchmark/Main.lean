import Autoinc
import Benchmark.List.Examples
import Benchmark.Experiment
import Benchmark.ExperimentReaderT
import Benchmark.Sequence

def main : IO Unit := do
  -- Case.execAll' Example1.Benchmark.cases (caption:="tail -> tail -> tail -> head")
  -- Case.execAll' Example2.Benchmark.cases (caption:="append -> append -> length")
  -- ExperimentReaderT.Case.execAll' Example3.Benchmark.cases_1.1 Example3.Benchmark.cases_1.2 (caption:="drop -> take -> all")
  -- ExperimentReaderT.Case.execAll' Example3.Benchmark.cases_2.1 Example3.Benchmark.cases_2.2 (caption:="drop -> take -> all")
  -- ExperimentReaderT.Case.execAll' Example4.Benchmark.cases_1.1 Example4.Benchmark.cases_1.2   (caption:="drop -> take -> any")
  -- ExperimentReaderT.Case.execAll' Example4.Benchmark.cases_2.1 Example4.Benchmark.cases_2.2   (caption:="drop -> take -> any")
  -- Case.execAll' Example7.Benchmark.cases (caption:="reverse -> tail -> cons -> reverse -> head")
  -- Case.execAll' Example8.Benchmark.cases (caption:="append -> cons -> tail -> reverse -> length")
  -- ExperimentReaderT.Case.execAll' Example9.Benchmark.cases_1.1 Example9.Benchmark.cases_1.2 (caption:="drop -> reverse -> drop -> reverse -> all")
  -- ExperimentReaderT.Case.execAll' Example9.Benchmark.cases_2.1 Example9.Benchmark.cases_2.2 (caption:="drop -> reverse -> drop -> reverse -> all")
  Case.execAll' Example11.Benchmark.cases₁ (caption := "ΔList.count (list as internal list representation)")
  Case.execAll' Example11.Benchmark.cases₂ (caption := "ΔList.count (tree as internal list representation)")
  execAll (caption := "Change.patch on list and tree")
