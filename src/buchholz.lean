import set_theory.cardinal_ordinal

inductive buchholz_on : Type
| leaf -- 0
| add (v : ℕ) (b₁ b₂ : buchholz_on) -- Ψᵥ(b₁) + b₂

namespace buchholz_on

instance : has_zero buchholz_on := ⟨leaf⟩

def psi (v : ℕ) (α : buchholz_on) := add v α 0

instance : has_one buchholz_on := ⟨psi 0 0⟩

def lt' : buchholz_on → buchholz_on → Prop
| 0 α                        := α ≠ 0
| _ 0                        := ff
| (add v α β) (add v' α' β') := v < v' ∨ (v = v' ∧ (lt' α α' ∨ (α = α' ∧ lt' β β')))

instance : has_lt buchholz_on := ⟨lt'⟩

instance : has_le buchholz_on := ⟨λ a b, a < b ∨ a = b⟩

def built_from_below (v : ℕ) (α : buchholz_on) : buchholz_on → Prop
| 0             := tt
| (add v' α' β) := built_from_below α' ∧ built_from_below β ∧ (v' < v ∨ α' < α)

def normal_form : buchholz_on → Prop
| 0                     := tt
| (add v α 0)           := normal_form α ∧ built_from_below v α α
| (add v α (add u β γ)) := normal_form α ∧ built_from_below v α α ∧ normal_form (add u β γ) ∧ β ≤ α

end buchholz_on

universe u

namespace ordinal

def init_segment (α : ordinal.{u}) : set ordinal.{u} := λ x, x < α

/-- Enumerates the alephs, as ordinals. -/
noncomputable def aleph (α : ordinal.{u}) : ordinal.{u} := (cardinal.aleph α).ord

theorem aleph_lt_aleph {α β : ordinal.{u}} : α.aleph < β.aleph ↔ α < β := begin
  unfold aleph,
  rw cardinal.ord_lt_ord,
  exact cardinal.aleph_lt
end

theorem aleph_le_aleph {α β : ordinal.{u}} : α.aleph ≤ β.aleph ↔ α ≤ β := begin
  unfold aleph,
  rw cardinal.ord_le_ord,
  exact cardinal.aleph_le
end

noncomputable def Omega : ℕ → ordinal.{u}
| 0 := 1
| v := ordinal.aleph v

theorem zero_lt_Omega (v : ℕ) : 0 < Omega v := begin
  induction v,
  { exact zero_lt_one },
  apply lt_of_lt_of_le omega_pos,
  rw ←cardinal.ord_omega,
  exact cardinal.ord_le_ord.mpr (cardinal.omega_le_aleph _),
end

end ordinal

/-- Ordinals less than ℵₙ. -/
def lt_aleph (n : ℕ) : set ordinal.{u} := (ordinal.aleph.{u} n).init_segment

/-- Ordinals less than ℵ_ω. -/
def lt_aleph_omega : set ordinal.{u} := (ordinal.aleph ordinal.omega.{u}).init_segment

/-
instance (n : ℕ) : has_lift (lt_aleph n) (lt_aleph_omega) :=
{ lift := λ α, ⟨α.val, begin
    have : α.val < ordinal.aleph n := (α.prop : α.val < ordinal.aleph n),
    apply lt_trans this,
    rw ordinal.aleph_lt_aleph,
    exact ordinal.nat_lt_omega _
  end ⟩}
  -/

/-- A Ψ-family is an ordered sequence of functions, the v-th of which maps the ordinals less than
α to ℵ_(v+1). Buchholz Ψ functions form a Ψ-family. -/
def psi_family (α : ordinal.{u}) : Type (u + 1) := α.init_segment → Π v : ℕ, lt_aleph.{u} (v + 1)

/-- `C v α Ψ` consists of all the ordinals that may be built from
* ordinals up to `Ωᵥ`,
* additions,
* application of the `Ψ` functions on inputs less than `α`.
-/
inductive C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : ordinal.{u} → Prop
| base (β < ordinal.Omega.{u} v) : C β
| add {β γ : ordinal.{u}} (hβ : C β) (hγ : C γ) : C (β + γ)
| psi (v : ℕ) {β : α.init_segment} (hβ : C β.val) : C (Ψ β v).val

/-- `0` always belongs to `C v α Ψ`. -/
theorem zero_mem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : C v α Ψ 0 :=
C.base 0 (ordinal.zero_lt_Omega v)

theorem aleph_mem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) {β : ordinal.{u}} :
  C v α Ψ β → β < ordinal.aleph (v + 1) :=
begin
  intro h,
  cases h, -- does not fail???
end

theorem aleph_nmem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : ¬ C v α Ψ (ordinal.aleph (v + 1)) :=
λ h, (lt_irrefl _) (aleph_mem_C v α Ψ h)

/-- Minimum excluded ordinal of a family of ordinals. -/
noncomputable def ordinal.mex (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) : ordinal.{u} :=
ordinal.omin (λ α, α ∉ S) ⟨α, hα⟩

theorem ordinal.mex_le_nmem (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) :
  ordinal.mex S hα ≤ α :=
by { apply ordinal.omin_le, exact hα }

theorem ordinal.lt_mex_of_mem (S : set ordinal.{u}) {α β : ordinal} (hα : α ∉ S)
  (hβ : β < ordinal.mex S hα) :
  β ∈ S :=
by { by_contra hβ', exact not_le_of_gt hβ (ordinal.omin_le hβ') }

/-- Minimum excluded ordinal of `C v α Ψ`. -/
noncomputable def C_mex (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : lt_aleph (v + 1) :=
⟨ordinal.mex (C v α Ψ) (aleph_nmem_C v α Ψ), begin
  sorry,
end⟩

noncomputable def buchholz_psi' : ordinal.{u} → Π v, lt_aleph (v + 1) :=
well_founded.fix ordinal.wf (λ α Ψ v, C_mex v α (λ ⟨β, hβ⟩, Ψ β hβ))

/-- The Buchholz `Ψ` function. -/
noncomputable def buchholz_psi (v : ℕ) (α : ordinal.{u}) : ordinal.{u} := buchholz_psi' α v