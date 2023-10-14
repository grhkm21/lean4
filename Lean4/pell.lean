import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.Sort
import Std.Tactic.SimpTrace

-- (x^2+n)/(2x)

def rat_sqrt_aux (n : ℚ) (q : ℚ) : ℕ → ℚ
| 0 => q
| (k + 1) => rat_sqrt_aux n (q - (q ^ 2 - n) / (2 * q)) k

def rat_sqrt_approx (q : ℚ) : ℚ :=
  if q < 0 then
    0
  else
    (Nat.sqrt q.num.natAbs : ℚ) / (Nat.sqrt q.den)

def rat_sqrt (q : ℚ) : ℚ := rat_sqrt_aux q (rat_sqrt_approx q) 6

theorem will_converge (q : ℚ) (hq : q.den ≠ 1) : (q - q.floor)⁻¹.den < q.den := sorry

def continued_fraction : ℚ → List ℤ
| q =>
  if h : q.den = 1 then
    [q.num]
  else
    let _ := will_converge q h
    q.floor :: continued_fraction (1 / (q - q.floor))
  termination_by _ q => q.den

def func' (n : ℕ) (a0 : ℕ) (data : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  -- a * s - r, (n - (a * s - r) ^ 2) / s)
  let (a, r, s) := data
  let r' : ℕ := a * s - r
  let s' : ℕ := (n - r' ^ 2) / s
  let a' : ℕ := (r' + a0) / s'
  (a', r', s')

-- clearly aux naming
def cf_sqrt_aux (n k n0 : ℕ) : List (ℕ × ℕ × ℕ) :=
  match k with
  | 0 => [(n0, 0, 1)]
  | k + 1 =>
    let data := cf_sqrt_aux n k n0
    data ++ [func' n n0 data.getLast!]

theorem cf_sqrt_aux_ne_empty : cf_sqrt_aux n k n0 ≠ [] := by
  cases k
  rintro ⟨⟩
  rw [cf_sqrt_aux]
  apply List.append_ne_nil_of_ne_nil_right
  apply List.ne_nil_of_length_eq_succ
  apply List.length_singleton

def cf_sqrt (n k : ℕ) : List ℕ := (cf_sqrt_aux n k n.sqrt).map (λ s => s.1)

-- such great naming! this is only for *computation* not for *proving*
def cf_sqrt_convs (n k : ℕ) : List ℚ := Id.run do
  if k = 0 then
    return []
  else if k = 1 then
    return [n.sqrt]
  else
    let data := cf_sqrt n k
    let a1 ← data[1]!
    let mut f0 : ℚ := n.sqrt
    let mut f1 : ℚ := ((a1 * f0.num + 1) / (a1 * f0.den : ℚ))
    let mut res : Array ℚ := Array.mkArray k 0
    res ← res.set! 0 f0
    res ← res.set! 1 f1
    for i in [2 : k] do
      let ai := data[i]!
      res ← res.set! i ((ai * f1.num + f0.num) / (ai * f1.den + f0.den : ℚ))
      f0 ← f1
      f1 ← res[i]!
    return res.toList

-- finds minimal (x, y) such that x^2 - dy^2 = 1
-- only considers first 50 convergents (Sage says it's enough)
def solve_pell (d : ℕ) : Option (ℕ × ℕ) := Id.run do
  let data := cf_sqrt_convs d 50
  for q in data do
    let x := q.num.natAbs
    let y := q.den
    if x ^ 2 - d * y ^ 2 = 1 then
      return some (x, y)
  return none

-- instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
--     Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
--   decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
--     ball_congr fun _ _ => imp_congr lt_succ_iff Iff.rfl

-- (859, 2058844771979643060124010, 70246877103894937291269)
#eval ((((List.range' 1 1000).filter (λ k => k.sqrt ^ 2 ≠ k)).map (λ k => (k, (solve_pell k).get!))).mergeSort (λ x y : ℕ × ℕ × ℕ => x.2.1 > y.2.1))[1]!
