import YM.Integration.ManuscriptQLocalMayerCoordinates
import YM.Integration.WilsonRootedMayerHull
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Satin

/-! Integrate the complete fitted component in the one joint marginal of the
original physical Gaussian, at each held exterior and Haar coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMayerWindow
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Greenbelt Lotus Daisy RGLocalTaylor RGLocalTaylor.Mayer
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {W s μ C : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R} {j : ℕ}

open MeasureTheory ConnectedActivityE6.Poll ConnectedActivityE6.Pond
open ConnectedActivityE6.Census WilsonRootedMayerHull

/-- The paid covariance remains coupled on the entire support. Both the
coordinate count and the exact signed integral precede the held Haar test. -/
theorem fitted (H:Cash W s μ L Q o C T R) (p:Molecule S) (X:Coat T F)
    (date:X.x=s) (width:X.width=o.K) (live:X.manifest) :
    let E:=coordinates H p X
    (E.card:ℝ)≤H.shapeW p*(Animals.ballCost (radiusB s):ℝ)*(tubularPrice G S.patch.L:ℝ) ∧
    MeasurePreserving (swim E) X.dice (arch E X.relating) ∧
    ∀ {r:Insert T}, Fits H r (H.unionP p) j → ∀ y:F.Slice G,
      (∫ z:Air f G,r.joint X (y,z) ∂X.dice)=
      ∫ z:Body (↥E),r.joint X (y,spill E z) ∂arch E X.relating := by
  intro E
  have project : MeasurePreserving (swim E) X.dice (arch E X.relating) :=
    Pond.orbit (H.laws.data.localP F X date width live).sails.fullC.posSemidef E
  refine ⟨ManuscriptQLocalMayerCoordinates.charged H p X.B,project,?_⟩
  intro r fits y
  apply Pond.gathered (spill E) (spill_m E) project (settled E)
  · exact fun z w h=>WilsonRootedMayerHull.fitted fits X date width y z w h
  · exact fits.along (V:=fun _=>X.V) (Z:=fun (_:Air f G)=>y) (z:=id) X date width
      (Air f G) measurable_const measurable_const measurable_id

/-- Every previously signed, marked and forced partner is still in the
integrand, together with the prescribed regular decoration of the remainder. -/
theorem decorated (H:Cash W s μ L Q o C T R) (prior:Team R) (p:Molecule S)
    {M:ℕ} (u:Decors (p\prior.signs S) M) (X:Coat T F)
    (date:X.x=s) (width:X.width=o.K) (live:X.manifest) (y:F.Slice G) :
    let E:=coordinates H p X
    let r:=Mayer.tagged H p (Laminate.partner prior H) u
    (∫ z:Air f G,r.joint X (y,z) ∂X.dice)=
      ∫ z:Body (↥E),r.joint X (y,spill E z) ∂arch E X.relating := by
  have hf (i : Head S) (hi : i∈p\(p\prior.signs S)) :
      Fits H (Laminate.partner prior H i) (H.supportP i) 0 := by
    have hs:i∈prior.signs S:=by
      by_contra h
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,h⟩)
    exact (Laminate.partnerFit (H:=H) (j:=0) hs).1
  exact (fitted H p X date width live).2.2 (Mayer.fits_tagged H (Laminate.partner prior H) hf u) y

end YM.Integration.WilsonMovingMayerWindow
end
