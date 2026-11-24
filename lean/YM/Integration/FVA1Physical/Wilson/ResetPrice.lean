import YM.Integration.FVA1Physical.Wilson.InheritedPrice

/-! Controlling the use of a period-independent predicted reset history.
The increment is the very kinetic response of the formal chain attached
to the run. Its error is charged to the physical selected step. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Filter Lattice RG Tree Marker PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PertExtension.Series.Tested Pert.Asymptotics
open FormalOPE.RG10.InversionTop
open scoped Classical BigOperators

variable {G : Gauge} (A : Run G)

/-- All increments of the formal kinetic reset of this cutoff, before choosing a period. -/
def predictedClock (N j : ℕ) : ℝ := - ∑ i ∈ Finset.range j, (RunFormalChain.fromRun A).kin.alpha N i

/-- An upper bound for the error of the physical reset, selected before period and cutoff. -/
def resetPrice (j : ℕ) : ℝ :=
  min (UVNext.CouplingReset.width A.alloy.B.a j A.kit.post)
    (AnalyticBridge.VerifiedReset.Time.forecastE A.alloy.B.a j / (A.alloy.B.a.budget j).threshold^2)

private theorem step_price (hs : G.Simple) {N j p : ℕ} (hj : j < N) :
    |A.family.path.β N p j - A.family.path.β N p (j+1) - (RunFormalChain.fromRun A).kin.alpha N j| ≤
      resetPrice A j := by
  obtain ⟨l,v,Q,K,x,he,hf,_⟩ := A.carries N j p hj
  obtain ⟨_,h₁,h₂,_⟩ := (K.moves hs hj).2 x.val x.property
  change |((Extra.Histories.Issue.trail A.T).rep N p j).beta - ((Extra.Histories.Issue.trail A.T).rep N p (j+1)).beta - A.alloy.B.kin.alpha N j| ≤ _
  rw [he,hf]
  rw [UVNext.CouplingReset.predictor, sub_add_eq_sub_sub] at h₁ h₂
  exact le_min h₁ ((le_div_iff₀ (pow_pos (A.alloy.B.a.budget j).threshold_pos _)).mpr
    (by simpa only [mul_comm] using h₂))

private def accumulated (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, resetPrice A i

private theorem acc_mono (hs : G.Simple) : Monotone (accumulated A) := by
  apply monotone_nat_of_le_succ
  intro j
  have hp := (abs_nonneg _).trans (step_price A hs (N:=j+1) (p:=0) (Nat.lt_succ_self j))
  simpa only [accumulated, Finset.sum_range_succ, le_add_iff_nonneg_right] using hp

/-- Error bill for the retained history. Each stage is charged once. -/
def historyResetPrice (m N : ℕ) : ℝ := accumulated A N - accumulated A m

private theorem integrated_reset (hs : G.Simple) (p : ℕ) {m N : ℕ} (hm : m ≤ N) :
    ‖(A.family.path.β N p m - predictedClock A N m) -
      (A.family.path.β N p N - predictedClock A N N)‖ ≤ historyResetPrice A m N := by
  induction hm using Nat.decreasingInduction with
  | self => simp [historyResetPrice]
  | of_succ m h ih =>
    let e (j : ℕ) := A.family.path.β N p j - predictedClock A N j
    have he : ‖e m - e (m+1)‖ ≤ resetPrice A m := by
      rw [show e m-e (m+1) = A.family.path.β N p m - A.family.path.β N p (m+1) -
          (RunFormalChain.fromRun A).kin.alpha N m by
        simp only [e, predictedClock, Finset.sum_range_succ]; ring]
      exact step_price A hs h
    calc
      ‖e m-e N‖ ≤ ‖e m-e (m+1)‖+‖e (m+1)-e N‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ resetPrice A m+historyResetPrice A (m+1) N := add_le_add he ih
      _ = historyResetPrice A m N := by simp only [historyResetPrice,accumulated,Finset.sum_range_succ]; ring

/-- A clock chosen entirely from the run's formal chain before any external
period or probe, with an independently purchased uniform physical error. -/
def predictedOffset (N m i : ℕ) := predictedClock A N (m+i) - predictedClock A N N

theorem predicted_offset_price (hs : G.Simple) {N m p : ℕ}
    (T : Slices A.family.path.levels p) (hm : m ≤ N) :
    (traversal T hm).Band (historyResetPrice A m N) (actualOffset A.family p N m - predictedOffset A N m) := by
  intro i hi
  rw [traversal_depth] at hi
  have hp := integrated_reset A hs p (show m+i ≤ N by omega)
  have hz := acc_mono A hs (Nat.le_add_right m i)
  change ‖(A.family.path.β N p (m+i)-A.family.path.β N p N)-
    (predictedClock A N (m+i)-predictedClock A N N)‖ ≤ _
  rw [show (A.family.path.β N p (m+i)-A.family.path.β N p N)-
    (predictedClock A N (m+i)-predictedClock A N N) =
      (A.family.path.β N p (m+i)-predictedClock A N (m+i))-
      (A.family.path.β N p N-predictedClock A N N) by ring]
  exact hp.trans (sub_le_sub_left hz _)

variable {V : Type} [DecidableEq V] (R : Census V) {N m p d : ℕ}
    (U : V → Stamp.Reservation A.family (A.family.side N p) d)
    (T : Slices A.family.path.levels p) (hm : m ≤ N)
    (H : (traversal T hm).Room G) (t : (traversal T hm).Tags)

/-- Analytic comparison of the actual normalized interacting reading to the
period-independent planned clock. The last term is an explicit sum of paid
physical reset costs, including the forecast energy divided by the squared threshold. -/
theorem predicted_history_price (hs : G.Simple) (r : ℕ) :
    let g := regulatorRun A.family N p N
    let D := traversal T hm
    ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ (∀ a : ℝ, 0 < a → ∀ s : R.Mode,
      ‖a⁻¹ ^ weight R (MSMatch.SourceTop.grade U) s •
        (D.moments R (offset (actualOffset A.family p N m) a) (MSMatch.SourceTop.field U) 1).part s -
        peval (historyCoefficient R U D (RunFormalChain.fromRun A).O H t (predictedOffset A N m) s) r a‖ ≤
          B*a^(r+1) + E*a^2*historyResetPrice A m N) ∧ ∀ s : R.Mode,
      ‖g⁻¹ ^ weight R (MSMatch.SourceTop.grade U) s •
        ((((A.family.path.rep N p m).eval 1 : ℝ) : ℂ)⁻¹ *
          (D.marks R (line A.family.path p m N) (MSMatch.SourceTop.field U) 1).part s) -
        peval (historyCoefficient R U D (RunFormalChain.fromRun A).O H t (predictedOffset A N m) s) r g‖ ≤
          B*g^(r+1) + E*g^2*historyResetPrice A m N := by
  dsimp only
  let D := traversal T hm
  let a := actualOffset A.family p N m
  let z := predictedOffset A N m
  let δ := historyResetPrice A m N
  let M := resetBill A.family m hm + δ
  have hδ : D.Band δ (a-z) := predicted_offset_price A hs T hm
  have ha := roof_guard A.makes T hm
  have h₀ : 0 ≤ δ := nonnegativeBand hδ
  have hb : D.Band M a := fun i hi => (ha i hi).trans (le_add_of_nonneg_right h₀)
  have hz : D.Band M z := by
    intro i hi
    calc
      ‖z i‖ = ‖a i + (z i-a i)‖ := by rw [add_sub_cancel]
      _ ≤ ‖a i‖+‖z i-a i‖ := norm_add_le ..
      _ ≤ M := add_le_add (ha i hi) ((norm_sub_rev _ _).le.trans (hδ i hi))
  obtain ⟨B,E,hB,hE,P⟩ := perturbed_history_price R A U T hm H t z hz r
  have hP (g : ℝ) (hg : 0 < g) (s : R.Mode) := P g hg a δ hb hδ s
  refine ⟨B,E,hB,hE,hP, fun s => ?_⟩
  let g := regulatorRun A.family N p N
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive A.makes.wilson (le_refl N)))
  have h := hP g hg s
  rw [show offset a g = line A.family.path p m N from line_offset A.makes,
      conditional_mark, vacuum_eq T A.makes.wilson hm] at h
  exact h

end YM.Integration.FVA1Physical.Wilson

