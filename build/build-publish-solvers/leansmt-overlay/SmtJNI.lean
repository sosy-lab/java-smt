import Lean

import Smt.Translate.Commands
import Smt.Translate.Solver
import Smt.Translate.Term

open Smt
open Smt.Translate
open Smt.Translate.Solver

namespace smt

structure RuntimeState where
  nextSolver : UInt64 := 1
  nextTerm : UInt64 := 1
  solvers : Std.HashMap UInt64 SolverState := {}
  terms : Std.HashMap UInt64 Term := {}
  lastError : String := ""
  initialized : Bool := false
deriving Inhabited

initialize runtimeRef : IO.Ref RuntimeState ←
  IO.mkRef ({ } : RuntimeState)

private def getRuntime : IO RuntimeState :=
  runtimeRef.get

private def setRuntime (state : RuntimeState) : IO Unit :=
  runtimeRef.set state

private def clearError : IO Unit := do
  let state ← getRuntime
  setRuntime { state with lastError := "" }

private def setError (msg : String) : IO Unit := do
  let state ← getRuntime
  setRuntime { state with lastError := msg }

private def catchUInt64 (action : IO UInt64) : IO UInt64 := do
  try
    clearError
    action
  catch err =>
    setError err.toString
    pure 0

private def catchUInt32 (action : IO UInt32) : IO UInt32 := do
  try
    clearError
    action
  catch err =>
    setError err.toString
    pure 1

private def catchUInt8 (action : IO UInt8) : IO UInt8 := do
  try
    clearError
    action
  catch err =>
    setError err.toString
    pure 3

private def catchString (action : IO String) : IO String := do
  try
    clearError
    action
  catch err =>
    setError err.toString
    pure ""

private def insertSolver (solver : SolverState) : IO UInt64 := do
  let state ← getRuntime
  let handle := state.nextSolver
  setRuntime {
    state with
      nextSolver := handle + 1
      solvers := state.solvers.insert handle solver
  }
  pure handle

private def insertTerm (term : Term) : IO UInt64 := do
  let state ← getRuntime
  let handle := state.nextTerm
  setRuntime {
    state with
      nextTerm := handle + 1
      terms := state.terms.insert handle term
  }
  pure handle

private def getSolver (handle : UInt64) : IO SolverState := do
  let state ← getRuntime
  match state.solvers[handle]? with
  | some solver => pure solver
  | none => throw <| IO.userError s!"Invalid solver handle: {handle}"

private def getTerm (handle : UInt64) : IO Term := do
  let state ← getRuntime
  match state.terms[handle]? with
  | some term => pure term
  | none => throw <| IO.userError s!"Invalid term handle: {handle}"

private def updateSolver (handle : UInt64) (solver : SolverState) : IO Unit := do
  let state ← getRuntime
  setRuntime { state with solvers := state.solvers.insert handle solver }

private def removeSolver (handle : UInt64) : IO Unit := do
  let state ← getRuntime
  setRuntime { state with solvers := state.solvers.erase handle }

private def runSolver (handle : UInt64) (action : SolverM α) : IO α := do
  let solver ← getSolver handle
  let (result, solver') ← action.run solver
  updateSolver handle solver'
  pure result

private def parseSolverKind (kind : UInt8) : Kind :=
  match kind.toNat with
  | 0 => .cvc5
  | 1 => .z3
  | _ => .cvc5

private def configureSolver (kind : Kind) (solver : SolverState) : IO SolverState := do
  let action : SolverM Unit := do
    match kind with
    | .cvc5 =>
      Solver.setOption "produce-models" "true"
    | _ =>
      pure ()
  let (_, solver') ← action.run solver
  pure solver'

private def boolSort : Term :=
  .symbolT "Bool"

private def intSort : Term :=
  .symbolT "Int"

private def realSort : Term :=
  .symbolT "Real"

private def bitvecSort (width : UInt32) : Term :=
  .literalT s!"(_ BitVec {width})"

private def natLiteral (n : Nat) : Term :=
  .literalT (toString n)

private def intLiteral (value : Int) : Term :=
  if value < 0 then
    .appT (.symbolT "-") (natLiteral value.natAbs)
  else
    natLiteral value.natAbs

private def realLiteral (num den : Int) : Term :=
  let (num, den) :=
    if den < 0 then
      (-num, -den)
    else
      (num, den)
  if den == 1 then
    intLiteral num
  else
    let fraction := Term.mkApp2 (.symbolT "/") (natLiteral num.natAbs) (natLiteral den.natAbs)
    if num < 0 then
      .appT (.symbolT "-") fraction
    else
      fraction

private def bitvecLiteral (width : UInt32) (value : String) : Term :=
  .literalT s!"(_ bv{value} {width})"

private def unary (op : String) (arg : Term) : Term :=
  .appT (.symbolT op) arg

private def binary (op : String) (lhs rhs : Term) : Term :=
  Term.mkApp2 (.symbolT op) lhs rhs

private def ternary (op : String) (a b c : Term) : Term :=
  Term.mkApp3 (.symbolT op) a b c

private def indexedUnary (op : String) (index : UInt32) (arg : Term) : Term :=
  .appT (.literalT s!"(_ {op} {index})") arg

private def extractTerm (arg : Term) (msb lsb : UInt32) : Term :=
  .appT (.literalT s!"(_ extract {msb} {lsb})") arg

private def declareVariable (solver : UInt64) (name : String) (sort : Term) : IO UInt64 := do
  runSolver solver <| Solver.declareConst name sort
  insertTerm (.symbolT name)

private def withQueryProcess (query : String) : IO UInt8 := do
  let solver ← Solver.createFromKind .cvc5 none none
  solver.proc.stdin.putStr query
  if !query.endsWith "\n" then
    solver.proc.stdin.putStr "\n"
  solver.proc.stdin.flush
  let (_, proc) ← solver.proc.takeStdin
  let output ← proc.stdout.readToEnd
  let _ ← proc.stderr.readToEnd
  let _ ← proc.wait
  let result := output.trimAscii
  if result == "sat" then
    pure 0
  else if result == "unsat" then
    pure 1
  else if result == "unknown" then
    pure 2
  else
    throw <| IO.userError s!"Unexpected solver output: {output}"

private def readSolverSexp (solver : SolverState) : IO Sexp := do
  let mut line ← solver.proc.stdout.getLine
  let mut out := line
  let mut parseRes := Sexp.Parser.sexp.run out
  while !line.isEmpty && parseRes matches .error _ do
    line ← solver.proc.stdout.getLine
    out := out ++ line
    parseRes := Sexp.Parser.sexp.run out
  match parseRes with
  | .ok (.expr [ .atom "error", .atom e ]) =>
      throw <| IO.userError <| unquoteString e
  | .ok sexp => pure sexp
  | .error e =>
      let err ← solver.proc.stderr.readToEnd
      throw <| IO.userError <| parseErrMsg e out err
where
  unquoteString (s : String) : String :=
    if s.length >= 2 && s.startsWith "\"" && s.endsWith "\"" then
      String.Pos.Raw.extract s ⟨1⟩ ⟨s.length - 1⟩
    else
      s

  parseErrMsg (e : String) (out err : String) : String :=
    s!"could not parse solver output: {e}\nsolver stdout:\n{out}\nsolver stderr:\n{err}"

private def extractGetValue (response : Sexp) : IO String :=
  match response with
  | .expr [ .expr [ _, value ] ] => pure (toString value)
  | _ => throw <| IO.userError s!"unexpected get-value output: {response}"

@[export leansmt_init]
def leanSmtInit : IO UInt32 := do
  clearError
  let state ← getRuntime
  setRuntime { state with initialized := true }
  pure 0

@[export leansmt_get_error]
def leanSmtGetError : IO String := do
  let state ← getRuntime
  pure state.lastError

@[export leansmt_cleanup]
def leanSmtCleanup : IO Unit := do
  let state ← getRuntime
  for (_, solver) in state.solvers.toList do
    try
      let _ ← Solver.exit.run solver
      pure ()
    catch _ =>
      pure ()
  setRuntime {}

@[export leansmt_create_solver]
def leanSmtCreateSolver (kind : UInt8) : IO UInt64 :=
  catchUInt64 do
    let solverKind := parseSolverKind kind
    let solver ← Solver.createFromKind solverKind none none
    let solver ← configureSolver solverKind solver
    insertSolver solver

@[export leansmt_delete_solver]
def leanSmtDeleteSolver (handle : UInt64) : IO UInt32 :=
  catchUInt32 do
    let solver ← getSolver handle
    let _ ← Solver.exit.run solver
    removeSolver handle
    pure 0

@[export leansmt_set_logic]
def leanSmtSetLogic (handle : UInt64) (logic : @&String) : IO UInt32 :=
  catchUInt32 do
    runSolver handle <| Solver.setLogic logic
    pure 0

@[export leansmt_mk_bool_var]
def leanSmtMkBoolVar (solver : UInt64) (name : @&String) : IO UInt64 :=
  catchUInt64 <| declareVariable solver name boolSort

@[export leansmt_mk_int_var]
def leanSmtMkIntVar (solver : UInt64) (name : @&String) : IO UInt64 :=
  catchUInt64 <| declareVariable solver name intSort

@[export leansmt_mk_real_var]
def leanSmtMkRealVar (solver : UInt64) (name : @&String) : IO UInt64 :=
  catchUInt64 <| declareVariable solver name realSort

@[export leansmt_mk_bv_var]
def leanSmtMkBvVar (solver : UInt64) (name : @&String) (width : UInt32) : IO UInt64 :=
  catchUInt64 <| declareVariable solver name (bitvecSort width)

@[export leansmt_mk_int_const]
def leanSmtMkIntConst (value : Int) : IO UInt64 :=
  catchUInt64 <| insertTerm (intLiteral value)

@[export leansmt_mk_real_const]
def leanSmtMkRealConst (num den : Int) : IO UInt64 :=
  catchUInt64 <| insertTerm (realLiteral num den)

@[export leansmt_mk_bv_const]
def leanSmtMkBvConst (width : UInt32) (value : @&String) : IO UInt64 :=
  catchUInt64 <| insertTerm (bitvecLiteral width value)

@[export leansmt_mk_true]
def leanSmtMkTrue : IO UInt64 :=
  catchUInt64 <| insertTerm (.literalT "true")

@[export leansmt_mk_false]
def leanSmtMkFalse : IO UInt64 :=
  catchUInt64 <| insertTerm (.literalT "false")

@[export leansmt_mk_app1]
def leanSmtMkApp1 (op : @&String) (term : UInt64) : IO UInt64 :=
  catchUInt64 do
    let arg ← getTerm term
    insertTerm (unary op arg)

@[export leansmt_mk_app2]
def leanSmtMkApp2 (op : @&String) (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary op left right)

@[export leansmt_mk_extract]
def leanSmtMkExtract (term : UInt64) (msb lsb : UInt32) : IO UInt64 :=
  catchUInt64 do
    let arg ← getTerm term
    insertTerm (extractTerm arg msb lsb)

@[export leansmt_mk_indexed_app1]
def leanSmtMkIndexedApp1 (op : @&String) (index : UInt32) (term : UInt64) : IO UInt64 :=
  catchUInt64 do
    let arg ← getTerm term
    insertTerm (indexedUnary op index arg)

@[export leansmt_mk_not]
def leanSmtMkNot (term : UInt64) : IO UInt64 :=
  catchUInt64 do
    let arg ← getTerm term
    insertTerm (unary "not" arg)

@[export leansmt_mk_and]
def leanSmtMkAnd (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "and" left right)

@[export leansmt_mk_or]
def leanSmtMkOr (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "or" left right)

@[export leansmt_mk_xor]
def leanSmtMkXor (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "xor" left right)

@[export leansmt_mk_implies]
def leanSmtMkImplies (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "=>" left right)

@[export leansmt_mk_iff]
def leanSmtMkIff (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "=" left right)

@[export leansmt_mk_ite]
def leanSmtMkIte (cond thenBranch elseBranch : UInt64) : IO UInt64 :=
  catchUInt64 do
    let c ← getTerm cond
    let t ← getTerm thenBranch
    let e ← getTerm elseBranch
    insertTerm (ternary "ite" c t e)

@[export leansmt_mk_eq]
def leanSmtMkEq (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "=" left right)

@[export leansmt_mk_distinct]
def leanSmtMkDistinct (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "distinct" left right)

@[export leansmt_mk_lt]
def leanSmtMkLt (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "<" left right)

@[export leansmt_mk_le]
def leanSmtMkLe (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "<=" left right)

@[export leansmt_mk_gt]
def leanSmtMkGt (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary ">" left right)

@[export leansmt_mk_ge]
def leanSmtMkGe (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary ">=" left right)

@[export leansmt_mk_add]
def leanSmtMkAdd (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "+" left right)

@[export leansmt_mk_sub]
def leanSmtMkSub (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "-" left right)

@[export leansmt_mk_mul]
def leanSmtMkMul (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "*" left right)

@[export leansmt_mk_div]
def leanSmtMkDiv (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "div" left right)

@[export leansmt_mk_mod]
def leanSmtMkMod (lhs rhs : UInt64) : IO UInt64 :=
  catchUInt64 do
    let left ← getTerm lhs
    let right ← getTerm rhs
    insertTerm (binary "mod" left right)

@[export leansmt_mk_neg]
def leanSmtMkNeg (term : UInt64) : IO UInt64 :=
  catchUInt64 do
    let arg ← getTerm term
    insertTerm (unary "-" arg)

@[export leansmt_assert]
def leanSmtAssert (solver term : UInt64) : IO UInt32 :=
  catchUInt32 do
    let arg ← getTerm term
    runSolver solver <| Solver.assert arg
    pure 0

@[export leansmt_check_sat]
def leanSmtCheckSat (solver : UInt64) : IO UInt8 :=
  catchUInt8 do
    let result ← runSolver solver Solver.checkSat
    match result with
    | .sat => pure 0
    | .unsat => pure 1
    | .unknown => pure 2

@[export leansmt_get_model]
def leanSmtGetModel (solver : UInt64) : IO String :=
  catchString <| runSolver solver Solver.getModel

@[export leansmt_get_value]
def leanSmtGetValue (solver term : UInt64) : IO String :=
  catchString do
    let solverState ← getSolver solver
    let valueTerm ← getTerm term
    solverState.proc.stdin.putStr s!"(get-value ({valueTerm}))\n"
    solverState.proc.stdin.flush
    extractGetValue (← readSolverSexp solverState)

@[export leansmt_get_proof]
def leanSmtGetProof (solver : UInt64) : IO String :=
  catchString do
    let proof ← runSolver solver Solver.getProof
    pure (toString proof)

@[export leansmt_check_sat_string]
def leanSmtCheckSatString (query : @&String) : IO UInt8 :=
  catchUInt8 <| withQueryProcess query

end smt
