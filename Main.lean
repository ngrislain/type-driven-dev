import TypeDrivenDev

def main : IO Unit := do
  SortList.main
  IO.println ""
  FetchData.main
  IO.println ""
  CostlyResult.main
