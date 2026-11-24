import YM.Integration.FVA1Physical.Wilson.BareSolenoid
import YM.Integration.FVA1Physical.Wilson.SceneFirst

/-! The first nonflat physical vacuum density and the FVA2 history ledger, before
coupling recalibration. The Gaussian base power, chart Jacobian and full
coarse-field denominator are retained on both rays. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Function Filter Set MeasureTheory RG Lattice YM.Wilson Tree Precision
open FVA2.CityHistory FVA2.RayScatter FormalOPE.RG10.MultiGauge
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open PertExtension PertExtension.Series PertExtension.Series.Tested
open MSbar.Rolling Comparison.RG02
open scoped Classical Topology ContDiff

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    (Z : ChartRatio G) (t : S.Choices) (h : Bid.Larger (G := G) S)
    (v : (Descent.nil (top := f)).Tags)
local notation "d₀" => Descent.nil (top := f)
local notation "h₀" => (show (d₀).Room G from trivial)

/-- The absolute one-step FVA2 vacuum series at an arbitrary coarse ray. -/
def firstLedger (u : Pins G c) : PowerSeries ℝ :=
  let Q := gateQ S F t (retained d₀ v h₀)
  let hp := useful S F d₀ v t h h₀
  PowerSeries.C (basePower Q hp u (Chart.tangent G F.Free) 1 * Stack.overhead Z F.Free) *
    Stack.read u (μLedger (Descent.push S F d₀) Z (t,v) ⟨h,h₀⟩ 1)

theorem first_ledger_birth (hZ : LocalRatio Z) (u : Pins G c) {P : Oven S.patch}
    (X : P.Form G) (H : P.Offers X S.kernel) (hu : ∀ i, ‖u i‖ ≤ X.Q) :
    PowerSeries.mk (Fk.birth (Spool.lens (S := S) u X F) Z) = firstLedger S F Z t h v u := by
  rw [Fork.uniform_nil (Spool.lens (S := S) u X F) Z hZ (Spot.thermalHeat S F t h)
    (gateQ S F t (retained d₀ v h₀)) (Spot.precisionHeat S F t h v)
    (useful S F d₀ v t h h₀) u (Spot.prospect S F t u h P X H hu)]
  unfold firstLedger
  rw [judgment S F d₀ v t Z 1 h h₀,Pi.one_apply,Spot.fusionL S F Z t h v]

include h in
/-- The phase factor and the exact kernel prefactor cancel between the two
coarse rays. The remaining denominator is the physical Haar push at identity. -/
private theorem phase_ratio {P : Oven S.patch} (X : P.Form G) (u : Pins G c) {g : ℝ} (hg : 0 < g) :
    Fk.phaseAmt (Spool.lens (S := S) u X F) univ 1 g /
      Fk.phaseAmt (Spool.lens (S := S) (0 : Pins G c) X F) univ 1 g =
    shunt S (breed G f) g (Oven.slice u g) := by
  have hz : Oven.slice (0 : Pins G c) g = 1 := by
    funext i
    simp [Oven.slice]
  rw [shunt_is_physical,breed,Integral.temperature,← inv_pow,← hz]
  change _ = spinVac S u g / spinVac S (0 : Pins G c) g
  rw [quiet S u F h.1,quiet S (0 : Pins G c) F h.1,
    mul_div_mul_left _ _ (Next.Fluctuations.Sector.prefactor_pos _).ne']
  unfold Fk.phaseAmt
  simp only [Pi.one_apply,mul_one,setIntegral_univ,mul_div_mul_left _ _ (Real.exp_pos _).ne',
    mul_div_mul_left _ _ (show (g^Module.finrank ℝ (Fk.Panel G F.Free))⁻¹ ≠ 0 by positivity)]
  rfl

/-- All finite orders of the true nonflat physical vacuum on a fixed regulator,
in the independent FVA2 ledger with the full origin normalization. -/
theorem first_ledger_density (hZ : LocalRatio Z) (P : Oven S.patch) (u : Pins G c) :
    Aspiration (fun g => shunt S (breed G f) g (Oven.slice u g))
      (Tested.term (firstLedger S F Z t h v u * (firstLedger S F Z t h v 0)⁻¹)) := by
  obtain ⟨X,H,hu,cap⟩ := Spot.enough S F h P u
  have cap₀ (i) : ‖(0 : Pins G c) i‖ ≤ X.Q := by simpa using H.good.thick.1.le
  have h₀' := Spot.runs S F (0 : Pins G c) h P X H cap₀
  have gift : Visible X (fun _ : Empty → G.Color => 1) (1 : Melody G F.Free) Fk.vacant 0 1 :=
    ⟨fun _ _ => RG.Envelope.const (1 : ℝ),fun _ _ _ => (abs_one (α := ℝ)).le,∅,
      by simp,fun j => Empty.elim j,fun _ _ _ _ _ => rfl⟩
  have hp := (Fk.aspirant hu hZ gift contDiffAt_const).quotient
    (Fk.aspirant h₀' hZ gift contDiffAt_const) (Fk.basis_fee h₀' hZ).ne'
  change Aspiration _ (Tested.term (PowerSeries.mk (Fk.birth (Spool.lens (S := S) u X F) Z) *
      (PowerSeries.mk (Fk.birth (Spool.lens (S := S) (0 : Pins G c) X F) Z))⁻¹)) at hp
  rw [first_ledger_birth S F Z t h v hZ u X H cap,
    first_ledger_birth S F Z t h v hZ 0 X H cap₀] at hp
  intro k
  exact Laplace.bill_congr (Tested.eventually_pos.mono fun g hg =>
    congrArg (fun y => y - peval _ k g) (phase_ratio S F h X u hg)) (hp k)

end YM.Integration.FVA1Physical.Wilson
