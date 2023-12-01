import Mathlib.Tactic

open String Tactic

def parseDigit (c : Char) : ℕ := if '0' ≤ c ∧ c ≤ '9' then c.val.toNat - 0x30 else 0

def parseNatAux : List Char → ℕ
| [] => 0
| x :: xs => (parseNatAux xs) * 10 + parseDigit x

def parseNat : String → ℕ := fun s ↦ parseNatAux (s.toList.reverse)

def getInput : IO (Array String) :=
  let dir := "/Users/grhkm/coding/lean4/Lean4"
  IO.FS.lines (dir ++ "/in")

def words : List String := [
  "0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
  "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"
]

def List.enumerate (l : List α) : List (ℕ × α) := (List.range l.length).zip l

def getNumberAux : List (ℕ × String) → String → Option ℕ
| [], _ => none
| (i, w)::ws, s => if s.startsWith w then some (i % 10) else getNumberAux ws s

def getNumber (b : Bool) (s : String) : Option ℕ :=
  getNumberAux (if b then words else words.take 10).enumerate s

partial def String.getFirst : Bool → String → Option ℕ
| _, "" => none
| b, s => match getNumber b s with
  | none => getFirst b (s.drop 1)
  | some n => n

partial def String.getLast : Bool → String → Option ℕ
| _, "" => none
| b, s => match getLast b (s.drop 1) with
  | none => getFirst b s
  | some n => n

def part (b : Bool) : IO ℕ := do
  let mut res := 0
  let input ← getInput
  for line in input do
    let num := match (line.getFirst b, line.getLast b) with
    | (some m, some n) => m * 10 + n
    | (_, _) => 0
    res := res + num
  return res

def part1 : IO ℕ := do
  part true

def part2 : IO ℕ := do
  part false

#eval timeit "" part1
#eval timeit "" part2
