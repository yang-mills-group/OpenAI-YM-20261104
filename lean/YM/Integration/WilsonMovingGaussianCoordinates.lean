import YM.Integration.WilsonMovingGaussianGeometry

/-! Exact affine coordinates of the finite moving posterior on every
original link. Trunk links vanish in its linear chart, and the deterministic
coarse copy enters the mean of the genuine free forest coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingGaussianCoordinates
open Function Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Next.Free
open scoped Topology Matrix ContDiff Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

def link (G : Gauge) (n : Side) : Primary n G ≃ Reef.wire G n where
  toFun u := (u.1.1,u.1.2,u.2)
  invFun u := ((u.1,u.2.1),u.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original fine forest lift written in the actual measured coordinate
order. This is a single complete fine field, before field positions are tested. -/
def planted (F : Forest S.ratio) (z : Positions (Key F G)) : Positions (Primary f G) :=
  fun i => if h : (i.1.1,axisEquiv.symm i.1.2)∈F.trunks then 0
    else z (⟨(i.1.1,axisEquiv.symm i.1.2),h⟩,i.2)

theorem stored (F : Forest S.ratio) (z : Positions (Key F G)) :
    planted F z = (Reef.offer G F (z ∘ (Reef.pines F).symm)) ∘ link G f := by
  funext i
  obtain ⟨⟨o,b⟩,a⟩ := i
  let u : Reef.wire G f := (o,b,a)
  by_cases h : (o,axisEquiv.symm b)∈ F.trunks
  · rw [planted,dif_pos h]
    exact (Flat.bring_dead F (z ∘ (Reef.pines F).symm) (i:=u)
      (by change ¬ ((o,axisEquiv.symm b)∉F.trunks); exact not_not.mpr h)).symm
  · rw [planted,dif_neg h]
    let k : Key F G := (⟨(o,axisEquiv.symm b),h⟩,a)
    have index : ((Reef.pines F k).val : Reef.wire G f)=u := by
      change (o,axisEquiv (axisEquiv.symm b),a)=u
      rw [Equiv.apply_symm_apply]
    have read := Flat.bring_alive F (z ∘ (Reef.pines F).symm) (Reef.pines F k)
    rw [index,Function.comp_apply,Equiv.symm_apply_apply] at read
    exact read.symm

variable {p : Clip} {A : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p A O) (F : Forest S.ratio)

/-- The derivative of the actual stationary section, in the exact
incoming coordinate order of the observed forest. -/
theorem differential (b : Positions (Primary c G)) :
    fderiv ℝ (fun u : Positions (Primary c G) =>
      (tint G F.Free).symm (K.b F ((tint G (Body 1 c)) u))) 0 b =
      FreeResolvent.active F (fderiv ℝ (K.b F) 0 ((tint G (Body 1 c)) b)) := by
  let P := tint G (Body 1 c)
  let E := (tint G F.Free).symm
  have zero : P 0=0 := map_zero _
  have d := ((K.critical F).2.1.differentiableAt (by norm_num)).hasFDerivAt
  have first := (zero.symm ▸ d).comp 0 P.toContinuousLinearMap.hasFDerivAt
  have full := E.toContinuousLinearMap.hasFDerivAt.comp 0 first
  have eq : fderiv ℝ (fun u => E (K.b F (P u))) 0 =
      E.toContinuousLinearMap.comp ((fderiv ℝ (K.b F) 0).comp P.toContinuousLinearMap) := full.fderiv
  rw [eq]
  rfl

/-- The physical and independently prescribed means agree after restoring
the exact coarse-link copy. The original fine coordinate is not centered twice. -/
theorem onRun (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)
    (b : Positions (Primary (R.family.S.side i per) G)) :
    let S := R.family.path.levels.clock.op i per
    let K := (RunFormalChain.fromRun R).step N i per hi
    let x := (tint G (Body 1 (R.family.S.side i per))) b
    let Q := Bloch.installed S.ratio ((destination R.family.path.levels N i).duo
      R.family.path.levels.clock.kernel.penalty).A0
    fderiv ℝ (fun u => (tint G F.Free).symm (K.b F (tint G _ u))) 0 b +
        (fun j : Key F G => linearCopy S.ratio (collect G x) j.1.val j.2) =
      fun j => (Flat.rawMean G S F Q *ᵥ FreeResolvent.flatten x) (Reef.pines F j) := by
  intro S K x Q
  rw [differential K F b]
  exact WilsonCommonConditionalGaussian.mean R N i per hi F tag x

end YM.Integration.WilsonMovingGaussianCoordinates
