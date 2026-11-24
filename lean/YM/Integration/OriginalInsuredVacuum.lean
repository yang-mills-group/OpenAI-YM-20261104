import YM.RG01Estimate.Covering
import YM.RG01Estimate.InheritedSales
import YM.Integration.OriginalQuadraticVacuum
import YM.Integration.RunRG02Along

/-! The original Wilson fine representation in the native unmarked insured
input. Its entire genuine regular debit and all forced rows are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalInsuredVacuum

open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.Board RG01Estimate.Evoc
open IterationFour IterationFour.Currency
open scoped Classical Topology

variable {G : Gauge}

private def emptyAddresses (f : Side) : Lex Empty f :=
  ⟨fun x => x.2.elim, fun {x} => x.2.elim⟩

/-- All regular labels are included in the inherited error. There are no
additional analytic input labels, so the native support stamp is empty. -/
def native (R : Run G) (N per m d : ℕ) (hm : m < N) :
    Insured R.alloy N m d (R.alloy.B.a.S.oneStep m per).exact_size
      (R.family.path.rep N per (m+1)).beta Empty := by
  have h := R.makes.wilson.represents N per (m+1) (Nat.succ_le_of_lt hm)
  refine {
    rep := R.family.path.rep N per (m+1)
    pathU := CommonConstruction.runAlong_actual_path R N (m+1) per (Nat.succ_le_of_lt hm)
    clip := h.clip
    β' := rfl
    point := h.vac
    legal := h.good.labels
    sacrifice := Set.univ
    music := emptyAddresses _
    coverage := ?_
    cost := ⟨fun x => x.2.elim, fun x => x.2.elim⟩ }
  intro i
  constructor
  · rintro ⟨x, _⟩
    exact x.2.elim
  · intro hi
    exact False.elim (hi trivial)

/-- The native receipt on its original full collection of regular indices.
The representation, path, kinetic unit and forced labels are literal. -/
theorem debit (R : Run G) (N per m d : ℕ) (hm : m < N) :
    let I := native R N per m d hm
    I.rep = R.family.path.rep N per (m+1) ∧ I.sacrifice = Set.univ ∧
      Inherit.Debits I.rep I.sacrifice (R.family.path.levels.clock.allowance (m+1)) := by
  intro I
  refine ⟨rfl, rfl, ?_⟩
  have he : Inherit.selected I.rep Set.univ = I.rep.activities := by
    simp only [Inherit.selected, Set.mem_univ, if_true]
  change (Inherit.selected I.rep Set.univ).EBound I.rep.p _
  rw [he]
  exact I.legal.boundE

/-- The original allowance pays its closed native exponent with an
explicit all-cutoff, all-period coefficient. -/
theorem at_native_power (R : Run G) (N per m d : ℕ) (hm : m < N) :
    let I := native R N per m d hm
    Inherit.Debits I.rep I.sacrifice
      ((2:ℝ)^(11/5:ℝ)*g R.family N per (m+1)^(11/5:ℝ)) :=
  Inherit.loosens _ _ _ (debit R N per m d hm).2.2
    (g_weight R.makes (Nat.succ_le_of_lt hm) (11/5) (by norm_num)).1

/-- Below the native exponent every prescribed positive coefficient is
paid before selecting the fine Wilson cutoff, period, or requested width. -/
theorem below (R : Run G) (hG : G.Simple) {s ε : ℝ}
    (hs : 0 ≤ s) (hs' : s < 11/5) (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop,
      ∀ (N per d : ℕ) (hm : m < N), let I := native R N per m d hm
        Inherit.Debits I.rep I.sacrifice (ε*g R.family N per (m+1)^s) := by
  have h2 : 0 < (2:ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
  have hbuy := buy R.family.path.levels hG 1 (div_pos hε h2) hs'
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hbuy] with m hpay
  intro N per d hm I
  apply Inherit.loosens _ _ _ (debit R N per m d hm).2.2
  calc
    weight R.family.path.levels (11/5) (m+1) ≤
        ε/2^s * weight R.family.path.levels s (m+1) := by
      simpa only [one_mul] using hpay
    _ ≤ ε/2^s * (2^s*g R.family N per (m+1)^s) :=
      mul_le_mul_of_nonneg_left (g_weight R.makes (Nat.succ_le_of_lt hm) s hs).1
        (div_nonneg hε.le h2.le)
    _ = _ := by field_simp [h2.ne']

end YM.Integration.OriginalInsuredVacuum
end
