import YM.Integration.FVA1Physical.TwoReset.StableRead

/-! The normalized finite Wick functional depends only on the common vacuum and the marked germ through the order read. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalStableCoverInput
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Comparison.RG02.Assembly
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G:Gauge} {V : Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {c f : Side} {B : StepData c f} {P : Clip} {Y' : PathData G} {O : ChartRatio G}
variable (K : Kernel B P Y' O) (A : Forest B.ratio) (ν : B.Choices)
variable (Y Z : Colors R G f) (p:ℕ) (h0 : Y.power=Z.power)
    (hy : ∀ j, GradeAt (Y.power j) (projected (Y.mark j)))
    (hz : ∀ j, GradeAt (Z.power j) (projected (Z.mark j)))
    (he : ∀ i≤p,∀ v, Air.discharge Y i (Stationary.arm G f 1 v) =
      Air.discharge Z i (Stationary.arm G f 1 v))

include h0 hy hz he
omit [Fintype V] in
private theorem field_step (j:Multi.Hot R)(i:ℕ)(hi:i≤p)(x : Bulk.Joint (G:=G) B A) :
    Assembly.markLetter Y.power (Bulk.markFn B A Y) j x i =
      Assembly.markLetter Z.power (Bulk.markFn B A Z) j x i := by
  let u(v:ℝ)(x:Config G f):= Y.mark j v x-Z.mark j v x
  let n := Z.power j
  have hf : projected u = projected (Y.mark j)-projected (Z.mark j):= rfl
  let hp := hy j
  let ht := hz j
  have hE : Assembly.GradeAt (n+p+1) (projected u) := by
    rw [hf]; constructor
    · exact hp.smooth.sub ht.smooth
    intro i h
    rw [iteratedFDeriv_sub_apply (hp.smooth.of_le le_top) (ht.smooth.of_le le_top)]
    apply sub_eq_zero.mpr
    by_cases hr:i<n
    · exact (hp.vanish i (congr_fun h0 j ▸ hr)).trans (ht.vanish i hr).symm
    apply equal_delta hp.smooth ht.smooth; refine tangent _ _ i (fun x=>?_)
    obtain ⟨v,rfl⟩:∃ v, x = (Stationary.arm G f 1) v := by
      obtain ⟨v,h⟩:= (Stationary.arm G f 1).surjective x; exact ⟨v,h.symm⟩
    obtain ⟨k,hk⟩:= Nat.exists_eq_add_of_le (Nat.le_of_not_gt hr)
    have h' := congr_arg (fun y:Poly R=> y.part j.val) (he k (by omega) v)
    change (Multi.lit R _).part j.val=(Multi.lit R _).part j.val at h'
    simp only [part_lit,h0] at h'
    exact hk.symm ▸ h'
  have h := (Bulk.joint_receipt B A hE).vanish (n+i) (by omega)
  rw [show posed B A u = Bulk.posed B A (Y.mark j) - Bulk.posed B A (Z.mark j) from rfl,
    iteratedFDeriv_sub_apply ((Bulk.joint_receipt B A hp).smooth.of_le le_top)
      ((Bulk.joint_receipt B A ht).smooth.of_le le_top)] at h
  unfold Assembly.markLetter Assembly.jet Bulk.markFn; unfold n at h; rw [h0,sub_eq_zero.mp h]


/-- Signed finite Wick equality, including all proper marked subsets. -/
theorem finite (vac : Y.vac = Z.vac) (x : Exterior.fieldDir G c 1) :
    Bulk.Fk K A ν Y x p = Bulk.Fk K A ν Z x p := by
  apply same_prescription K A ν Y Z p _ _ x
  · intro d _ z
    rcases Y with ⟨vy,my,py⟩
    rcases Z with ⟨vz,mz,pz⟩
    change vy = vz at vac
    subst vz
    rfl
  · exact field_step A Y Z p h0 hy hz he

end YM.Integration.WilsonOriginalStableCoverInput
