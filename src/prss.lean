import data.list.defs
import tactic

namespace list

/-- Splits a list right after the first element satisfying a predicate. -/
def split_at_pred {α : Type*} (l : list α) (P : α → Prop) [decidable_pred P] : list α × list α :=
l.split_at (l.find_index P).succ

/-- `l.split' k` splits `l` right after the first element equal to `k`. -/
def split_eq {α : Type*} (l : list α) (k : α) [decidable_eq α] : list α × list α :=
l.split_at_pred (eq k)

/-- Splits a list into the bad and good parts. -/
def split_prss : list ℕ → list ℕ × list ℕ
| []             := ([], [])
| (0 :: l)       := ([], l)
| ((n + 1) :: l) := l.split_eq n

/-- Appends a list to itself `n` times. -/
def cycle {α : Type*} : list α → ℕ → list α
| _ 0       := []
| l (n + 1) := l ++ (l.cycle n)

/-- The empty list cycled over and over is still the empty list. -/
theorem cycle_nil {α : Type*} {n : ℕ} : ([] : list α).cycle n = [] :=
begin
  induction n with n hn,
  { refl },
  change ([] : list α).cycle n.succ with [] ++ [].cycle n,
  rw hn,
  refl
end

/-- `l.prss n` performs one step of PrSS expansion, and copies the bad part `n` times. -/
def prss (l : list ℕ) (n : ℕ) : list ℕ :=
let (b, g) := l.split_prss in (b.cycle n) ++ g

/-- Leading zeros just get removed. -/
theorem prss_zero (l : list ℕ) {n : ℕ} : prss (0 :: l) n = l :=
begin
  change (0 :: l).prss n with _ ++ _,
  rw cycle_nil,
  refl
end

/-- Standard PrSS lists. -/
inductive is_standard : list ℕ → Prop
| base (n : ℕ) : is_standard (list.range n)
| tail (l : list ℕ) : is_standard l.tail
| prss (n : ℕ) (l : list ℕ) : is_standard (l.prss n)

/-- PrSS lists reachable from another. -/
inductive reachable (l : list ℕ) : list ℕ → Prop
| prss (n : ℕ) : reachable (l.prss n)

theorem termination {l : list ℕ} (hl : is_standard l) : l.reachable [] :=
sorry

end list