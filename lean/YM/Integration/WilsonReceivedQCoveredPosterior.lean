import YM.Integration.WilsonReceivedCompactQUnitTerminal

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedQCoveredPosterior
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
open Filter MergeProof.Accent RG3.Law OPE.Therm Extra.Trajectories Extra.Histories Trace.Physical.GermGraph
variable {G:Gauge} (R:Run G) {N per:ℕ}
local notation "C₀" => R.family
local notation "H₀" => R.family.path

/-- The two root comparisons and the ordinary conditional use the one physical probability at the lower date. -/
theorem original {t b u:ℕ} (live:t ≤ N) (bt:b ≤ t) (ub:u ≤ b)
    (f seam soft:Config G (R.family.side t per) → ℂ) (forced:Config G (R.family.side b per) → ℂ)
    (z:ℂ) (E D S:ℝ)
    (hf:Integrable (fun U=>(R.family.path.rep N per t).eval U • f U) (prior G _))
    (hZ:Integrable (fun U=>(R.family.path.rep N per t).eval U • seam U) (prior G _))
    (hs:Integrable (fun U=>(R.family.path.rep N per t).eval U • soft U) (prior G _))
    (spring:∀U,‖soft U‖ ≤ S)
    (heard:∀V,‖actualTransport (C₀) (N:=N) f (ub.trans bt) V-actualTransport (C₀) (N:=N) forced ub V-z‖ ≤ D)
    (seamFee:(∫V,‖actualTransport (C₀) (N:=N) seam (ub.trans bt) V‖ ∂scene (H₀) N per u) ≤ E) :
    (∫V,‖actualTransport (C₀) (N:=N) (f+seam-soft) (ub.trans bt) V-
      actualTransport (C₀) (N:=N) forced ub V-z‖ ∂scene (H₀) N per u) ≤ E+D+S := by
  let ut:=ub.trans bt
  have total:Integrable (fun U=>(R.family.path.rep N per t).eval U • (f+seam-soft) U) (prior G _) := by
    simp only [Pi.sub_apply,Pi.add_apply,smul_add,smul_sub];exact (hf.add hZ).sub hs
  have exactRows := WilsonReceivedQUnitCompulsory.add R ut (f+seam-soft) soft total hs
  rw [sub_add_cancel,WilsonReceivedQUnitCompulsory.add R ut f seam hf hZ] at exactRows
  have point V:‖actualTransport (C₀) (N:=N) (f+seam-soft) ut V-actualTransport (C₀) (N:=N) forced ub V-z‖ ≤
      ‖actualTransport (C₀) (N:=N) seam ut V‖+(D+S) := by
    have raw:=congrFun exactRows V
    simp only [Pi.add_apply] at raw
    have rearranged:actualTransport (C₀) (N:=N) (f+seam-soft) ut V-actualTransport (C₀) (N:=N) forced ub V-z =
      actualTransport (C₀) (N:=N) seam ut V+
        ((actualTransport (C₀) (N:=N) f ut V-actualTransport (C₀) (N:=N) forced ub V-z)-actualTransport (C₀) (N:=N) soft ut V) := by
      linear_combination -raw
    rw [rearranged]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans
      (add_le_add (heard V) (actualTransport_norm_le (C₀) R.makes live spring ut V))))
  have fee:=actualScene_integrable_of_weighted (C₀) R.makes (ut.trans live)
    (actualTransport_weighted_integrable_of_integrable (C₀) R.makes live hZ ut)
  letI:IsProbabilityMeasure (scene (H₀) N per u):=OPE.Therm.probability R.makes.wilson (ut.trans live)
  calc
    _ ≤ ∫V,‖actualTransport (C₀) (N:=N) seam ut V‖+(D+S) ∂scene (H₀) N per u :=
      integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (fee.norm.add (integrable_const _)) (ae_of_all _ point)
    _ = (∫V,‖actualTransport (C₀) (N:=N) seam ut V‖ ∂scene (H₀) N per u)+(D+S) := by
      rw [integral_add fee.norm (integrable_const _)];simp
    _ ≤ E+(D+S) := add_le_add seamFee le_rfl
    _ = E+D+S := by ring

end YM.Integration.WilsonReceivedQCoveredPosterior
