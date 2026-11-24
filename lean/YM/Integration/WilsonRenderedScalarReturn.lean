import YM.Integration.WilsonReceivedWholeFieldHot
import YM.Integration.ActualWilsonAbsoluteTransport

/-! A complete signed ordinary face reading on the original Wilson law.
The finite coefficients can include the scalar inverse of the independently
filed face table. They are fixed before integration over the older field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRenderedScalarReturn
open Finset MeasureTheory Lattice Wilson RG Ac Marker QuadraticLocal Multi
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums OPE.Therm
open WilsonRootedKioskOccupiedSlip WilsonReceivedWholeFieldHot
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {p : BudgetPoint} {V I T : Type}
  [DecidableEq V] [Fintype V] {Γ : Census V} {o : V → Site n}
  (L : Lamps T I G p o Γ) (t : T) (c : Γ.Mode → ℂ)

/-- The zero, proper and full faces use one ordinary exponential. -/
def field (U : Config G n) : ℂ := ∑ s, c s * (Poly.pass (bare L t U)).part s

theorem issued [Countable I] {w : V → ℝ} {a D : ℝ}
    (hw : ∀ v, 0 < w v) (ha : 0 ≤ a) (gross : Gross L w p.B a D) :
    Envelope (field L t c) := by
  refine ⟨Finset.measurable_sum _ (fun s _ =>
    measurable_const.mul (borel L hw ha gross t s)), ?_⟩
  refine ⟨∑ s, ‖c s‖ * (charge s D / Poly.toll w s),fun U => ?_⟩
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro s _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (le_div_iff₀ (Poly.worth hw s)).2
  simpa only [mul_comm (Poly.toll w s)] using ordinary L hw ha gross t U s

variable (C : Family G) (law : C.Makes) {N per u b : ℕ}
local notation "X" i:max => Config G (C.side i per)
local notation "μ" i:max => scene C.path N per i

include law in
/-- Signed first difference on each original normalized conditional. The
incoming and terminal scalar are kept, including the action of the older
vacuum on deposited proper faces. -/
theorem telescope (stop : u ≤ b) (top : b ≤ N) (rows : ∀ i, X i → ℂ)
    (registered : ∀ i, u ≤ i → i ≤ b → Envelope (rows i))
    (source : X b → ℂ)
    (sourcePaid : Integrable (fun U => (C.path.rep N per b).eval U • source U) (prior G _))
    (c : ℂ) :
    (∫ U, source U ∂μ b) - c =
      (∫ U, source U - rows b U ∂μ b) -
        (∑ j ∈ Ico u b, ∫ U, rows j U - actualAverage C (N:=N) (rows (j+1)) U ∂μ j) +
          ((∫ U, rows u U ∂μ u) - c) := by
  let M (j : ℕ) := ∫ U, rows j U ∂μ j
  have weighted (j : ℕ) (hj : u ≤ j) (jb : j ≤ b) :=
    ActualWilsonAbsoluteTransport.weighted C law (jb.trans top) (registered j hj jb)
  have step : (∑ j ∈ Ico u b, ∫ U, rows j U - actualAverage C (N:=N) (rows (j+1)) U ∂μ j) =
      ∑ j ∈ Ico u b,(M j - M (j+1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨uj,jb⟩ := Finset.mem_Ico.mp hj
    exact actualScene_step_error C law (jb.trans_le top) (weighted j uj jb.le)
      (weighted (j+1) (uj.trans (Nat.le_succ j)) jb)
  have ends (v : ℕ) (uv : u ≤ v) : (∑ j ∈ Ico u v,(M j - M (j+1))) = M u - M v := by
    induction v, uv using Nat.le_induction with
    | base => simp
    | succ j uj ih => rw [Finset.sum_Ico_succ_top uj,ih]; abel
  rw [step,ends b stop,integral_sub (actualScene_integrable_of_weighted C law top sourcePaid)
    (actualScene_integrable_of_weighted C law top (weighted b stop le_rfl))]
  change _ = _ - (M u - M b) + (M u - c)
  dsimp only [M]
  abel

end YM.Integration.WilsonRenderedScalarReturn
