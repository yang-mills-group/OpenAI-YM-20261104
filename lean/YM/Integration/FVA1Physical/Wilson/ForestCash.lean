import YM.Integration.FVA1Physical.Wilson.HotelPurchase
import YM.MSbar.Lease.Bench

/-! Volume-independent, arbitrary-power prices for the actual forest change,
including the exponential height multiplying the native forced contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum Pressure
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge}

private lemma box_major (G : Gauge) (P : Patch) :
    Beam G P.L (fun x:ℝ=>(Mosaic.boxK (tip G P.L x):ℝ)) := by
  have hw : Beam G P.L (fun x=>(spotN (tip G P.L x):ℝ)) := by
    unfold spotN; simp only [Nat.cast_pow]; exact (Beam.shore P.L G).power 4
  have hv : Beam G P.L (fun x=>((2*voyageB (tip G P.L x)+8 :ℕ):ℝ)) := by
    push_cast; exact ((Beam.coin 2).mul (Beads G P)).add (Beam.coin 8)
  unfold Mosaic.boxK; simp only [Nat.cast_mul]
  exact (chargesA P _ hw).mul (chargesA P _ hv)

/-- The height of the forest resampling density is paid by the forced-sector
budget. Also the chart-copy discrepancy has arbitrary inverse-power decay.
The original unmarked gas at remote failures is unrestricted. -/
theorem forest_cash (J : Voice G) (cle : Clear G J) (H H' : Stage) (P : Patch) (K : KernelChoices)
    (p : Palisade) (exponent : ℝ) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let v := tip G P.L x
      let X := Mosaic.boxX v b
      let Y := Mosaic.boxY v b
      let U := youth A.F Y
      let height := Real.exp (Posture.wSize G A.pre.p H'.width H'.paths (ability v) (lbt v) A.pre.beta
          (voyageB v) Y.card X.card p (rot p v) (room v)) / Posture.moss G (v^(-(1:ℝ))) (board A.F X).card
      let fee := silkRoad H'.paths H'.width (ability v) (lbt v) A.pre.beta X.card (voyageB v) A.pre.p (radiusB v)
      Grants A.v A.pre A.F p 3 → A.Calibrate J p X Y z v 0 exponent →
      0 ≤ fee ∧ fee ≤ v^exponent ∧
      courage G P.L x * (A.pre.p.mass U (height*2)*Real.exp (U.card* (1:ℝ))) ≤ v^exponent := by
  let bx := fun x:ℝ=> Mosaic.boxK (tip G P.L x)
  let bySize := fun x:ℝ=> Mosaic.boxL (tip G P.L x) P
  have bxRate : Beam G P.L (fun x=>(bx x:ℝ)) := box_major G P
  have byRate : Beam G P.L (fun x=>(bySize x:ℝ)) := by
    unfold bySize boxL; simp only [Nat.cast_mul]; exact bxRate.mul (Beam.coin _)
  have f := funding P p H' 0 bx bySize bxRate byRate G
  have road := status G P H' bx bxRate
  have high := Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)
  filter_upwards [high.eventually_ge_atTop 1,f (exponent-1) exponent (by linarith),
    road (exponent-1) exponent (by linarith)] with x big gas integral
  intro A z b patch kernel season v X Y U height fee give paid
  have fill : coverNumber A.pre.p.B U ≤ bySize x := by
    have base := Mosaic.caseL A.F A.pre b v
    rw [patch] at base
    exact base
  have size : Y.card ≤ bx x := Mosaic.caseY b v
  have en := Era P p J H H' x season patch X Y A.F A.v bx give size paid.first.extendsX big
      ((norm_nonneg _).trans paid.first.awake)
  have money := brought P K p J H H' cle x season patch kernel X Y A.F A.v z paid.first give bx _ fill size 0 big
  refine ⟨en.1,en.2.1.trans ((le_abs_self _).trans integral),?_⟩
  have credit := money.2.2.trans ((le_abs_self _).trans gas)
  simpa only [Real.rpow_zero,mul_one] using credit

end YM.Integration.FVA1Physical.Wilson
