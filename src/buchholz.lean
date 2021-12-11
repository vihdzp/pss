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
| (add v' α' β) := built_from_below β ∧ (v' < v ∨ (built_from_below α' ∧ α' < α))

def normal_form : buchholz_on → Prop
| 0                     := tt
| (add v α 0)           := normal_form α ∧ built_from_below v α α
| (add v α (add u β γ)) := normal_form α ∧ built_from_below v α α ∧ normal_form (add u β γ) ∧ β ≤ α

end buchholz_on

universes u v

namespace ordinal

/-- An initial segment of the ordinals. -/
def init_segment (α : ordinal.{u}) : set ordinal.{u} := λ x, x < α

/-- The Ωᵥ function as defined by Buchholz. -/
noncomputable def Omega : ℕ → ordinal.{u}
| 0 := 1
| v := (cardinal.aleph v).ord

/-- Ωᵥ is positive. -/
theorem Omega_pos {v : ℕ} : 0 < Omega v :=
begin
  induction v,
  { exact zero_lt_one },
  apply lt_of_lt_of_le omega_pos,
  rw ←cardinal.ord_omega,
  exact cardinal.ord_le_ord.mpr (cardinal.omega_le_aleph _),
end

/-- Ωᵥ < ℵ_ω. -/
theorem Omega_lt_aleph_omega {v : ℕ} : Omega v < (cardinal.aleph omega).ord :=
begin
  induction v with v hv,
  { apply lt_of_lt_of_le one_lt_omega,
    rw [←cardinal.ord_omega, ←cardinal.aleph_zero, cardinal.ord_le_ord, cardinal.aleph_le],
    exact ordinal.zero_le _ },
  show (cardinal.aleph v.succ).ord < (cardinal.aleph omega).ord,
  rw [cardinal.ord_lt_ord, cardinal.aleph_lt],
  exact nat_lt_omega _
end

/-- Ordinals less than ℵₙ. -/
def lt_aleph (n : ℕ) : set ordinal.{u} := (cardinal.aleph.{u} n).ord.init_segment

/-- Ordinals less than ℵ_ω. -/
def lt_aleph_omega : set ordinal.{u} := (cardinal.aleph omega.{u}).ord.init_segment

/-- ℵₙ < ℵ_ω. -/
lemma aleph_n_lt_aleph_omega {n : ℕ} :
  (cardinal.aleph.{u} n).ord < (cardinal.aleph.{u} omega.{u}).ord :=
by { rw [cardinal.ord_lt_ord, cardinal.aleph_lt], exact nat_lt_omega _ }

instance (n : ℕ) : has_lift (lt_aleph n) lt_aleph_omega :=
⟨λ α, ⟨α.val, have _ < _, from α.prop, lt_trans this aleph_n_lt_aleph_omega⟩⟩

/-- ω ^ ℵₙ = ℵₙ. -/
theorem omega_pow_aleph_eq_self (α : ordinal.{u}) :
  (cardinal.aleph.{u} α).ord = omega.{u} ^ (cardinal.aleph.{u} α).ord :=
sorry

/-- Minimum excluded ordinal of a family of ordinals. -/
noncomputable def mex (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) : ordinal.{u} :=
omin (λ α, α ∉ S) ⟨α, hα⟩

/-- The minimum excluded ordinal is excluded. -/
theorem not_mex_mem (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) : mex S hα ∉ S :=
omin_mem (λ α, α ∉ S) _

/-- The minimum excluded ordinal is less or equal to any excluded ordinal. -/
theorem mex_le_not_mem (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) : mex S hα ≤ α :=
by { apply omin_le, exact hα }

/-- Any ordinal less than the minimum excluded one is included. -/
theorem mem_of_lt_mex (S : set ordinal.{u}) {α β : ordinal} (hα : α ∉ S) (hβ : β < mex S hα) :
  β ∈ S :=
by { by_contra hβ', exact not_le_of_gt hβ (omin_le hβ') }

theorem mex_lt_of_card (S : set ordinal.{u}) {α : ordinal} (hα : α ∉ S) :
  lift.{u + 1} (mex S hα) < (cardinal.mk S).succ.ord :=
sorry

end ordinal

/-- A Ψ-family is an ordered sequence of functions, the v-th of which maps the ordinals less than
α to ℵ_(v+1). Buchholz Ψ functions form a Ψ-family. -/
def psi_family (α : ordinal.{u}) : Type (u + 1) :=
α.init_segment → Π v : ℕ, ordinal.lt_aleph.{u} (v + 1)

/-- `C v α Ψ` consists of all the ordinals that may be built from
* ordinals up to `Ωᵥ`,
* additions,
* application of the `Ψ` functions on inputs less than `α`.
-/
inductive C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : set ordinal.{u}
| low {β : ordinal.{u}} (hβ : β < ordinal.Omega.{u} v) : C β
| add {β γ : ordinal.{u}} (hβ : C β) (hγ : C γ) : C (β + γ)
| psi (v : ℕ) {β : α.init_segment} (hβ : C β.val) : C (Ψ β v).val

/-- `0` always belongs to `C v α Ψ`. -/
theorem zero_mem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : C v α Ψ 0 :=
C.low ordinal.Omega_pos

/-- The sets `C` are bounded above by `ℵ_ω`. -/
theorem lt_aleph_omega_of_mem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) {β : ordinal.{u}} :
  C v α Ψ β → β < (cardinal.aleph ordinal.omega).ord :=
begin
  intro h,
  induction h with β hβ β γ hβ hγ hβ' hγ' v β,
  { exact lt_trans hβ ordinal.Omega_lt_aleph_omega },
  { rw ordinal.omega_pow_aleph_eq_self ordinal.omega at *,
    exact ordinal.add_lt_omega_power hβ' hγ' },
  { exact lt_trans (Ψ β v).prop ordinal.aleph_n_lt_aleph_omega }
end

/-- `ℵ_ω` does not belong to any set `C`. -/
theorem aleph_nmem_C (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) :
  ¬ C v α Ψ (cardinal.aleph ordinal.omega).ord :=
λ h, (lt_irrefl _) (lt_aleph_omega_of_mem_C v α Ψ h)

theorem C_card (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) :
  cardinal.mk (C v α Ψ) = cardinal.aleph.{u + 1} v :=
sorry

/-- Minimum excluded ordinal of `C v α Ψ`. -/
noncomputable def C_mex' (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : ordinal.{u} :=
ordinal.mex (C v α Ψ) (aleph_nmem_C v α Ψ)

theorem cardinal.aleph_lift (α : ordinal.{u}) :
  cardinal.aleph (ordinal.lift.{max v u} α) = cardinal.lift.{max v u} (cardinal.aleph.{u} α) :=
begin
  sorry
end

theorem C_mex_lt_aleph' (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) :
  ∃ β : ordinal.lt_aleph.{u} (v + 1), ¬ C v α Ψ β.val :=
begin
  refine ⟨⟨C_mex' v α Ψ, _⟩, ordinal.not_mex_mem _ _⟩,
  show C_mex' v α Ψ < (cardinal.aleph (v + 1)).ord,
  rw ←ordinal.lift_lt,
  suffices : (cardinal.aleph v).succ.ord = ordinal.lift (cardinal.aleph (v + 1)).ord,
  { rw ←this,
    have := ordinal.mex_lt_of_card (C v α Ψ) (aleph_nmem_C v α Ψ),
    rwa C_card v α Ψ at this },
  have : cardinal.aleph (v + 1) = (cardinal.aleph v).succ := cardinal.aleph_succ,
  rw [←this, cardinal.lift_ord, ←(cardinal.aleph_lift.{u (u + 1)} (↑v + 1))],
  simp,
end

theorem C_mex_lt_aleph (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) :
  C_mex' v α Ψ < (cardinal.aleph (v + 1)).ord :=
begin
  --apply lt_of_le_of_lt (ordinal.mex_le_not_mem),
 -- have := ordinal.mex (C v α Ψ) (@classical.some_spec _ (λ β, ¬ C v α Ψ β ) (C_mex_lt_aleph' v α Ψ)),
 -- cases C_mex_lt_aleph' v α Ψ with β hβ,
 sorry
end

/-- Minimum excluded ordinal of `C v α Ψ`. -/
noncomputable def C_mex (v : ℕ) (α : ordinal.{u}) (Ψ : psi_family α) : ordinal.lt_aleph.{u} (v + 1) :=
sorry
--⟨C_mex' v α Ψ, C_mex_lt_aleph v α Ψ⟩

noncomputable def buchholz_psi' : ordinal.{u} → Π v, ordinal.lt_aleph (v + 1) :=
well_founded.fix ordinal.wf (λ α Ψ v, C_mex v α (λ ⟨β, hβ⟩, Ψ β hβ))

/-- The Buchholz `Ψ` function. -/
noncomputable def buchholz_psi (v : ℕ) (α : ordinal.{u}) : ordinal.{u} := buchholz_psi' α v