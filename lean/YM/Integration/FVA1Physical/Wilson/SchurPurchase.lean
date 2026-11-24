import YM.Integration.FVA1Physical.Wilson.OrbitGaussian
import YM.Integration.FVA1Physical.Wilson.PurchasedOrbit
import YM.MSbar.Folia.Cinema

/-! The independent Wilson action on the native conditional Gaussian having exactly
the local inverse block Hessian, its Schur mean, blocking noise and Haar Jacobian.
Coverage holds on all exterior configurations, including empty conditional fibres. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum Pressure
open MSbar.Bakery.Portal MSbar.Mosaic MSbar.Bakery.Film MSbar.Kelvin Next.SectorChange
open scoped Classical Topology
variable {G : Gauge}

def schurOrbit (A : Mosaic.Issue G) (J : Voice G) (χ : ChartRatio G) (x : ℝ)
    (z : Positions (Primary A.c G)) (b : Site A.f) (B : Positions (Primary A.f G)→ℝ)
    (φ : Config G A.f → ℝ) (U : Config G A.f) : ℝ :=
  let X := boxX x b
  let Y := boxY x b
  let O := represent (tint G (Exterior.Body 1 A.c) z)
  let ν := vest (priced A.F A.v A.pre.clip A.pre.path) z
  let clip := hotel A.F X Y J O ν (pillow x) (room x)
  let copy := chambers A.F Y J O ν
  let P := interiorEnergy A.S O A.v copy A.pre.beta A.fClock B
  let M := mold A.pre A.F A.v
  let i := includeX (G:=G) A.F X
  gaussianOrbit A.F X Y clip χ (him J A.F Y O ν M X (linCash A.F z) U ∘ i)
    ((MSbar.Kelvin.pinch i M)⁻¹) A.fClock P φ U

theorem purchased_schur (J : Voice G) (cle : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D → ∀ (B : Positions (Primary A.f G)→ℝ), Continuous B →
      ∀ (φ : Config G A.f→ℝ), Envelope φ →
      innerOrbit A J (tip G P.L x) z b B φ=schurOrbit A J χ (tip G P.L x) z b B φ := by
  obtain ⟨p,offer⟩ := purchased_chart_chance J cle simple H H' P K branch hD 0
  obtain ⟨_,_,theatre⟩ := waiting p H H' J χ hχ cle P 3 0
  filter_upwards [offer,theatre,(Work.E09.betaF_growth G P.L).eventually_gt_atTop 1] with x paid seats high
  intro A z b patch kernel season hZ B hB φ hφ
  let v:=tip G P.L x
  let X:=boxX v b
  let Y:=boxY v b
  let O:=represent (tint G (Exterior.Body 1 A.c) z)
  let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
  let copy:=chambers A.F Y J O ν
  let area:=hotel A.F X Y J O ν (pillow v) (room v)
  let E:=interiorEnergy A.S O A.v copy A.pre.beta A.fClock B
  obtain ⟨give,cal,_,_⟩ := paid A patch kernel season z b hZ
  obtain ⟨_,suite⟩ := seats.enter _ _ patch season X Y A.F z A.v give (by rw [patch]; exact cal.first)
  rw [patch] at suite
  have pc:=season.case_
  rw [patch] at pc
  have hp : 0<A.pre.beta := (half_pos (zero_lt_one.trans high)).trans_le pc.beta
  have ht : 0<A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have hA : MeasurableSet area := (garden_main A.F X Y J O ν cle cal.first.extendsX).from_here
  have rentalB := (Posture.buy A.v give cle cal.first pc.lawful season.bends.1 pc.decent hp.le).currency
  have effect : Envelope E := by
    have mc := (informed A.F X Y J O ν cle cal.first.extendsX).1
    have hP := backdrop (chartLog_envelope (G:=G) (f:=A.f) A.fClock hB) mc
    have hR := backdrop (A.pre.exponentEnv pc.lawful) mc
    have eq : E = fun U=> (B (chartLog A.fClock (copy U)) + (-A.pre.exponent (copy U))) +
          (rental A.F J A.pre Y A.v O ν U) := by
      funext U; unfold E interiorEnergy rental; ring
    rw [eq]; exact (hP.add hR.neg).add rentalB
  funext U
  apply orbit_gaussian_kernel
  · exact hχ
  · exact (suite.positivity.submatrix (secureY A.F X G)).inv
  · exact ht
  · exact hA
  · exact effect
  · exact hφ
  exact fun i hi=>coverage J A.F X Y O U ν χ cle (linCash A.F z) suite.seat cal.first.extendsX hi

end YM.Integration.FVA1Physical.Wilson
