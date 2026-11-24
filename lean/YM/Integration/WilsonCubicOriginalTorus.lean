import YM.Integration.WilsonCubicPrintedTensor
import YM.Integration.WilsonVacuumPreResetJointBranch

/-! The cubic array of the independently filed finite-period action on a
genuine original healthy sheet. Coarse and fine links are graded together. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCubicOriginalTorus
open Filter Function Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree Precision Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open Stationary Work.F03 Work.G05 ConnectedActivityE6 SliceRows Shell Coat Matter
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def coordinates (G : Gauge) (f : Side) : Directions G f →L[ℝ] Link G f :=
  ((arm G f 1).symm : _ →L[ℝ] _).comp (LinearMap.toContinuousLinearMap {
    toFun := SliceRows.toLog (G:=G) (n:=f)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl })

def reading (A : ℕ → Atom G 3) (U : Config G f) : ℝ :=
  Patch.average fun s : Signed => Precision.uncut A (pull s 0 U)

theorem raw (A : ℕ → Atom G 3) (u : Directions G f) :
    reading A (RG.increment 1 u) = turnSeries A (coordinates G f u) := by
  change reading A (RG.increment 1 u) = reading A (represent (arm G f 1 ((arm G f 1).symm (toLog u))))
  rw [ContinuousLinearEquiv.apply_symm_apply,edits]

theorem original {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ C : ℝ}
    {o : Target.Order G W} {R : Rep G f} (H : Cash W x μ L Q o C T R)
    (X : Coat T F) (p : Molecule S) (he : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (d : ℕ) :
    let Z := (Matter.planted X p).wrapY Y
    let u := coordinates G f ∘ changes Finset.univ Z
    ∀ k ≤ d, iteratedFDeriv ℝ k (reading R.path.cubic ∘ field Finset.univ Z) 0 =
      iteratedFDeriv ℝ k (WilsonCubicPrintedTensor.polynomial R.path.cubic d ∘ blockTaylor d u) 0 := by
  let Z := (Matter.planted X p).wrapY Y
  let U := field Finset.univ Z
  let u := coordinates G f ∘ changes Finset.univ Z
  let v := turnSeries R.path.cubic (m:=f)
  have at0 : U 0=1 := WilsonVacuumPreResetJointBranch.base X p he sun Y
  have agree : reading R.path.cubic ∘ U =ᶠ[𝓝 0] v ∘ u := by
    filter_upwards [agrees Finset.univ Z] with z hz
    change reading R.path.cubic (U z) = turnSeries R.path.cubic (coordinates G f (changes Finset.univ Z z))
    rw [show U z=RG.increment (U 0) (changes Finset.univ Z z) from hz,at0,raw]
  have zero : u 0=0 := by simp [u,changes_zero]
  have ht : ContDiffAt ℝ d u 0 :=
    (coordinates G f).contDiff.contDiffAt.comp _ ((smooth Finset.univ Z).of_le le_top)
  have hb := H.laws.intake.cap.paths
  have hv : ContDiffAt ℝ d v 0 := (turns_analytic R.path.cubic hb.width hb.three).contDiffAt.of_le le_top
  have z0 : blockTaylor d u 0=0 := (blockTaylor_zero d u).trans zero
  have filed := WilsonCubicPrintedTensor.printed (c:=f) R.path.cubic hb.width hb.three d
  have changeJets := jets_comp (x:=0) (g:=v) (g':=blockTaylor d v) ht (blockTaylor_contDiff d u _).contDiffAt
    (zero.symm ▸ hv) (blockTaylor_contDiff d v _).contDiffAt (zero.trans z0.symm)
    (fun k hk => (blockTaylor_jets ht k hk).symm)
    (fun k hk => by rw [z0]; exact (blockTaylor_jets hv k hk).symm)
  dsimp only
  intro k hk
  rw [filed]
  exact ((agree.iteratedFDeriv ℝ k).eq_of_nhds).trans (changeJets k hk)

end YM.Integration.WilsonCubicOriginalTorus
