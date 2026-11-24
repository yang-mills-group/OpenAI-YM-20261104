import YM.Integration.LocalComparisonGlobalContract

/-!
The original Run supplies both strong incoming K bounds at every valid stage.
Choose the fixed support exponents below the original positive initial profile.
Only the support mass and its unchanged block-cover parameter enter KBound;
the independently required field/distance admissions remain in Global.Input.
The actual representation identity is structural and is never inferred from
equality of evaluated densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStrongIntake

open Lattice Wilson RG Marker
open Comparison.RG02
open scoped Classical BigOperators

variable {G : Gauge}

def inputSupport (R : PhysicalNext.Repeat.Legato.Run G) : ℝ :=
  (R.family.path.levels.params 0).supportExponent / 2

def outputSupport (R : PhysicalNext.Repeat.Legato.Run G) : ℝ :=
  (R.family.path.levels.params 0).supportExponent / 4

theorem support_reserves (R : PhysicalNext.Repeat.Legato.Run G) :
    0 < outputSupport R ∧ outputSupport R < inputSupport R := by
  have h := (R.family.path.levels.params 0).price_pos
  dsimp only [inputSupport, outputSupport]
  constructor <;> linarith

theorem supports_le (R : PhysicalNext.Repeat.Legato.Run G) (m : ℕ) :
    inputSupport R ≤ (R.family.path.levels.budget m).supportExponent ∧
    outputSupport R ≤ (R.family.path.levels.budget m).supportExponent := by
  have h := R.family.path.levels.fits.deepExp (Nat.zero_le m)
  change (R.family.path.levels.params 0).supportExponent ≤
    (R.family.path.levels.params m).supportExponent at h
  have hp := (R.family.path.levels.params 0).price_pos
  constructor
  · change (R.family.path.levels.params 0).supportExponent / 2 ≤
      (R.family.path.levels.params m).supportExponent
    linarith
  · change (R.family.path.levels.params 0).supportExponent / 4 ≤
      (R.family.path.levels.params m).supportExponent
    linarith

theorem mass_mono {n : Side} {p q : BudgetPoint}
    (hB : p.B = q.B) (he : p.supportExponent ≤ q.supportExponent)
    (S : Support n) (c : ℝ) (hc : 0 ≤ c) :
    p.mass S c ≤ q.mass S c := by
  unfold BudgetPoint.mass
  rw [hB]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (by positivity))) hc

theorem kBound_mono {n : Side} (A : Activities G n) {p q : BudgetPoint} {w : ℝ}
    (hB : p.B = q.B) (he : p.supportExponent ≤ q.supportExponent)
    (h : A.KBound q w) : A.KBound p w := by
  obtain ⟨b, hb, hsum⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x
  let f : ℕ → ℝ := fun i =>
    if x ∈ (A.forced i).support then p.mass (A.forced i).support (b i) else 0
  let g : ℕ → ℝ := fun i =>
    if x ∈ (A.forced i).support then q.mass (A.forced i).support (b i) else 0
  have hg := hsum x
  change SumBudget g w at hg
  change SumBudget f w
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    dsimp only [f]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hb i).1
    · exact le_rfl
  have hfg : ∀ i, f i ≤ g i := by
    intro i
    dsimp only [f, g]
    split_ifs
    · exact mass_mono hB he _ _ (hb i).1
    · exact le_rfl
  have hs : Summable f := hg.2.1.of_nonneg_of_le hf hfg
  exact ⟨hf, hs, (hs.tsum_le_tsum hfg hg.2.1).trans hg.2.2⟩

theorem original (R : PhysicalNext.Repeat.Legato.Run G)
    (N q m : ℕ) (hm : m ≤ N) :
    (R.family.path.rep N q m).activities.KBound
      (R.family.path.levels.budget m)
      (R.family.path.levels.clock.forcedAllowance m) := by
  have h := R.makes.wilson.represents N q m hm
  have hp : (R.family.path.rep N q m).p =
      R.family.path.levels.budget m := h.vac
  have hk : (R.family.path.rep N q m).activities.KBound
      (R.family.path.rep N q m).p
      (R.family.path.levels.clock.forcedAllowance m) := h.good.labels.boundK
  simpa only [hp] using hk

theorem reserved (R : PhysicalNext.Repeat.Legato.Run G)
    (N q m : ℕ) (hm : m ≤ N) (p : BudgetPoint)
    {fieldOrder distanceOrder : ℕ}
    (hp : LocalComparison.NormAt R.family m p fieldOrder distanceOrder
      (inputSupport R)) :
    (R.family.path.rep N q m).activities.KBound p
      (R.family.path.levels.clock.forcedAllowance m) := by
  apply kBound_mono _ (q := R.family.path.levels.budget m) hp.block
  · rw [hp.reserve]
    exact (supports_le R m).1
  · exact original R N q m hm

theorem atRun {V : Type} [DecidableEq V] [Fintype V] {ρ : Census V}
    (R : PhysicalNext.Repeat.Legato.Run G)
    {J : LocalComparison.Global.Setup V}
    (A : LocalComparison.Global.Admission R.family J)
    (hJ : J.inputSupport = inputSupport R)
    {datum : LocalFormal.Datum R.family ρ}
    (I : LocalComparison.Global.Input (RunFormalChain.fromRun R) J A datum)
    (hactual : I.inputCarrier.rep =
      R.family.path.rep datum.cutoff datum.period (datum.level + 1)) :
    LocalComparison.Global.StrongIntake I := by
  have hm : datum.level + 1 ≤ datum.cutoff := Nat.succ_le_iff.mpr datum.below
  constructor
  · rw [hactual]
    exact original R datum.cutoff datum.period (datum.level + 1) hm
  · rw [hactual]
    exact reserved R datum.cutoff datum.period (datum.level + 1) hm
      (A.inputNorm datum.level) (by simpa only [hJ] using A.input_norm datum.level)

end YM.Integration.ActualRunStrongIntake
end
