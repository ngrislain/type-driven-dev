/-
  TypeDrivenDev.FetchData — Fetch CSV data over HTTPS and process with DataFrame

  Demonstrates:
  - `Hale.Req` for type-safe HTTP requests
  - `Hale.DataFrame` for CSV parsing, column selection, and filtering
-/
import Hale.Req
import Hale.DataFrame

open Network.HTTP.Req
open DataFrame

namespace FetchData

/-- Fetch the Iris CSV dataset from GitHub over HTTPS. -/
def fetchIrisData : IO DataFrame := do
  let url := https "raw.githubusercontent.com"
    /: "mwaskom" /: "seaborn-data" /: "master" /: "iris.csv"
  have : HttpBodyAllowed (HttpMethod.allowsBody (m := GET)) (HttpBody.providesBody (b := NoReqBody)) :=
    ⟨⟩
  let response : BsResponse ← runReq defaultHttpConfig (req GET.mk url NoReqBody.mk bsResponse)
  let csvText := String.fromUTF8! (BsResponse.responseBody response)
  return parseCsv csvText {}

def main : IO Unit := do
  IO.println "=== Req + DataFrame Demo ==="
  IO.println ""

  IO.println "Fetching Iris dataset from GitHub (HTTPS)..."
  let df ← fetchIrisData
  IO.println s!"Shape: {df.nRows} rows x {df.columns.size} columns"
  IO.println ""

  IO.println "--- First 5 rows ---"
  IO.println s!"{DataFrame.take df 5}"
  IO.println ""

  IO.println "--- Sepal dimensions only ---"
  IO.println s!"{DataFrame.take (DataFrame.select df ["sepal_length", "sepal_width"]) 5}"
  IO.println ""

  IO.println "--- Setosa species ---"
  let setosa := DataFrame.filterBy df "species" (fun | .str "setosa" => true | _ => false)
  IO.println s!"{setosa}"
  IO.println ""

  IO.println "--- Virginica species ---"
  let virginica := DataFrame.filterBy df "species" (fun | .str "virginica" => true | _ => false)
  IO.println s!"{virginica}"
  IO.println ""

  IO.println "=== Done ==="

end FetchData
