import data.list.defs
import tactic

universe u

namespace list

/-- Splits a list right after the first element satisfying a predicate. -/
def split_at_pred {α : Type u} (l : list α) (P : α → Prop) [decidable_pred P] : list α × list α :=
l.split_at (l.find_index P).succ

/-- `l.split' k` splits `l` right after the first element equal to `k`. -/
def split_eq {α : Type u} (l : list α) (k : α) [decidable_eq α] : list α × list α :=
l.split_at_pred (eq k)

/-- Splits a list into the bad and good parts. -/
def split_prss : list ℕ → list ℕ × list ℕ
| []             := ([], [])
| (0 :: l)       := ([], l)
| ((n + 1) :: l) := l.split_eq n

/-- Bad part of a list. -/
abbreviation bad_part (l : list ℕ) : list ℕ := l.split_prss.fst

/-- Good part of a list. -/
abbreviation good_part (l : list ℕ) : list ℕ := l.split_prss.snd

/-- The empty list splits into two copies of itself. -/
theorem split_prss_nil : list.nil.split_prss = ([], []) := rfl

/-- The bad and good parts together make the tail. -/
theorem bad_append_good_eq_tail : ∀ l : list ℕ, l.bad_part ++ l.good_part = l.tail
| []             := by refl
| (0 :: l)       := by refl
| ((n + 1) :: l) := begin
    change (split_at _ _).fst ++ (split_at _ _).snd = _,
    rw split_at_eq_take_drop _ l,
    exact take_append_drop _ l
  end

/-- Appends a list to itself `n` times. -/
def cycle {α : Type u} : list α → ℕ → list α
| _ 0       := []
| l (n + 1) := l ++ (l.cycle n)

/-- Cycling a list zero times gives the empty list. -/
theorem cycle_zero {α : Type u} (l : list α) : l.cycle 0 = [] := rfl

/-- Cycling a list once gives itself. -/
theorem cycle_one {α : Type u} (l : list α) : l.cycle 1 = l := l.append_nil

/-- Cycling the empty list gives itself. -/
theorem cycle_nil {α : Type u} : ∀ {n : ℕ}, ([] : list α).cycle n = []
| 0       := by refl
| (n + 1) := by { show nil ++ nil.cycle n = nil, by { rw cycle_nil, refl }}

/-- `l.prss n` performs one step of PrSS expansion, and copies the bad part `n` times. -/
def prss (l : list ℕ) (n : ℕ) : list ℕ :=
l.bad_part.cycle n ++ l.good_part

/-- Leading zeros just get removed. -/
theorem prss_lead_zero (l : list ℕ) {n : ℕ} : (0 :: l).prss n = l :=
begin
  change (0 :: l).prss n with list.cycle [] n ++ _,
  rw cycle_nil,
  refl
end

/-- `l.prss 1` just gives the tail. -/
theorem prss_one (l : list ℕ) : l.prss 1 = l.tail :=
begin
  change l.prss 1 with (list.cycle _ 1) ++ _,
  rw cycle_one,
  exact l.bad_append_good_eq_tail
end

/-- Standard PrSS lists. -/
inductive is_standard : list ℕ → Prop
| base (n : ℕ) : is_standard (list.range n)
| prss (l : list ℕ) (n : ℕ) : is_standard (l.prss n)

/-- Tails of standard lists are standard. -/
theorem tail_standard (l : list ℕ) : is_standard l.tail :=
begin
  convert is_standard.prss l 1,
  exact l.prss_one.symm,
end

/-- Returns the function that applies `g 0`, `g 1`, ... `g (n - 1)` to `f`, starting from `a`. -/
def apply {α β : Type u} (f : α → β → α) (a : α) (g : ℕ → β) : ℕ → α :=
λ n, foldl f a ((list.range n).map g)

/-- PrSS terminates. -/
theorem termination {l : list ℕ} (hl : is_standard l) (g : ℕ → ℕ) :
  ∃ n, apply list.prss l g n = [] :=
sorry

end list