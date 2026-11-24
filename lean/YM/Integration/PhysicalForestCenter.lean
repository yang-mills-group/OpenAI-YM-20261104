import YM.Integration.PhysicalForestRay

/-! At the original linearized stationary center the change between absolute
and relative integration variables has identity derivative on the free
variables and zero derivative on the coarse variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestCenter

open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open FreeResolvent Comparison.RG02 Stationary Next.SectorChange
open PhysicalForestAction PhysicalForestRay
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable {p : Clip} {P : PathData G} {O : ChartRatio G}
variable (M : Matrix (Woods G f) (Woods G c) ℝ) (K : Bulk.Kernel S p P O)

def copy (x : fieldDir G c 1) : Lawn (Active G F) := fun i =>
  linearCopy S.ratio (collect G x) i.1.val i.2

def predict (x : fieldDir G c 1) : Lawn (Active G F) :=
  reduce G S F *ᵥ (M *ᵥ flatten x)

private def pullFree : fieldDir G f 1 →L[ℝ] AxisChart G F :=
  ContinuousLinearMap.pi fun e => ContinuousLinearMap.proj (e.val.1,coord e.val.2)

private lemma fullLog (ρ : fieldDir G c 1 → AxisChart G F) (w : Sloc S F G) :
    glow S F (sedan S F ρ w) = pullFree S F (Work.F03.axisLog F (physical S F ρ w)) := by
  funext e
  change G.plog (G.mat (tip S F (sedan S F ρ w) e)) =
    G.plog (G.mat (Work.F03.live F (physical S F ρ w) (e.val.1,axisEquiv.symm (coord e.val.2))))
  rw [←coord_map,axisEquiv.symm_apply_apply]
  exact congrArg (fun q => G.plog (G.mat q)) (F.off_tree _ e).symm

private lemma pull_stretch (x : fieldDir G c 1) (a : AxisChart G F) :
    (vcloth S F G).symm (pullFree S F (Bid.stretch (S:=S) F (x,a))) = copy S F x + active F a := by
  funext i
  change ((linearCopy S.ratio (collect G x) (i.1.val.1,axisEquiv.symm (coord i.1.val.2))) +
    (if h : (i.1.val.1,axisEquiv.symm (coord i.1.val.2)) ∈ F.trunks then 0
      else a ⟨(i.1.val.1,axisEquiv.symm (coord i.1.val.2)),h⟩)) i.2 = _
  rw [←coord_map,axisEquiv.symm_apply_apply,dif_neg i.1.property]
  rfl

local notation "D" => fderiv ℝ (K.b F) 0
local notation "θ" => shore S F M (D)

variable (hC : ∀ x : fieldDir G c 1, active F ((fderiv ℝ (K.b F) 0) x) = predict S F M x - copy S F x)

include hC in
theorem sampled_derivative (x : fieldDir G c 1) (z : Precision.Key F G → ℝ) :
    HasDerivAt (fun g : ℝ => θ (g • sample S F x z)) z 0 := by
  let a : Work.F03.ChartVars F G := (x,D x + tape z)
  have hp (g : ℝ) : physical S F D (g • sample S F x z) = g • a := by
    have h := congrArg Prod.snd (exact_sample S F K x z g)
    rw [Bulk.footing] at h
    exact h
  have hr : HasDerivAt (fun g : ℝ => Work.F03.inclusion F (g • a))
      (x,Bid.stretch F a) 0 := by
    rw [← Work.F03.inclusion_deriv (S:=S) F a]
    exact Push.side _ ((Work.F03.inclusion_smooth F).differentiableAt (by simp)) a
  have hL := (vcloth S F G).symm.hasFDerivAt.comp_hasDerivAt 0
    ((pullFree S F (G:=G)).hasFDerivAt.comp_hasDerivAt 0 hr.snd)
  have he (g : ℝ) : rise S F M id (rightArm (g • sample S F x z)) = g • predict S F M x := by
    change (((reveal G S F).transpose * M).mulVecLin) (g • flatten x) = _
    rw [map_smul]
    apply congrArg (fun v=>g • v)
    change ((reveal G S F).transpose*M) *ᵥ flatten x = _
    rw [←Matrix.mulVec_mulVec]
    rfl
  have hu : (fun g : ℝ => θ (g • sample S F x z)) = fun g =>
      (vcloth S F G).symm (pullFree S F (Work.F03.axisLog F (g • a))) - g • predict S F M x := by
    funext g
    rw [shore,fullLog,hp,he]
  have hs : HasDerivAt (fun g : ℝ => g • predict S F M x) (predict S F M x) 0 := by
    simpa using! (hasDerivAt_id' (0:ℝ)).smul_const (predict S F M x)
  have hd : HasDerivAt (fun g : ℝ =>
      (vcloth S F G).symm (pullFree S F (Work.F03.axisLog F (g • a))) - g • predict S F M x)
      ((vcloth S F G).symm (pullFree S F (Bid.stretch F a)) - predict S F M x) 0 := hL.sub hs
  rw [hu]
  convert hd using 1
  rw [show a = (x,D x + tape z) from rfl,pull_stretch]
  change z = copy S F x + (active F ((fderiv ℝ (K.b F) 0) x) + z) - predict S F M x
  rw [hC]
  abel

include hC in
theorem derivative (w : Sloc S F G) : fderiv ℝ θ 0 w = leftArm w := by
  have h := sampled_derivative S F M K hC (badge S F w) (leftArm w)
  have he : sample S F (badge S F w) (leftArm w) = w := by
    funext i
    cases i <;> rfl
  rw [he] at h
  have hd := Push.side _ ((shore_green S F M D (D).contDiff.contDiffAt (map_zero D)).differentiableAt
    (by simp)) w
  exact hd.unique h

include hC in
theorem grade_zero (i : Active G F) :
    constantCoeff (spool θ i) =
      constantCoeff (noiseLine (Y:=Woods G c) (1 : Matrix (Active G F) (Active G F) ℝ) i) := by
  classical
  have ht : Green θ := shore_green S F M D (D).contDiff.contDiffAt (map_zero D)
  have he (w : Sloc S F G) :
      fderiv ℝ (fun y => θ y i) 0 w = fderiv ℝ (fun y : Sloc S F G => leftArm y i) 0 w := by
    let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Active G F => ℝ) i
    have e : fderiv ℝ (fun y => θ y i) 0 w = L (fderiv ℝ θ 0 w) :=
      congrFun (congrArg DFunLike.coe
        (L.hasFDerivAt.comp 0 (ht.differentiableAt (by simp)).hasFDerivAt).fderiv) w
    rw [e, derivative S F M K hC w]
    exact congrFun (congrArg DFunLike.coe
      (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Active G F ⊕ Woods G c => ℝ) (.inl i)).hasFDerivAt.fderiv.symm) w
  have hq : constantCoeff (spool θ i) = constantCoeff (spool (leftArm (U:=Active G F) (V:=Woods G c)) i) := by
    simp only [spool,← coeff_zero_eq_constantCoeff_apply,coeff_mk,jet_apply]
    congr 1
    funext j
    simp only [rye,Nat.zero_add]
    apply congrArg (fun z:ℝ=>((1:ℕ).factorial:ℝ)⁻¹ • z)
    change iteratedFDeriv ℝ 1 (fun u=>θ u i) 0 _ =
      iteratedFDeriv ℝ 1 (fun u:Sloc S F G=>leftArm u i) 0 _
    rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,he]
  rw [hq,unit_pin]
  have hf : leftArm (U:=Active G F) (V:=Woods G c) = fun u => leftFlag (Active G F) (Woods G c) *ᵥ u :=
    (funext left_hit).symm
  rw [hf,spool_board,loom_pin,Finset.sum_eq_single (Sum.inl i)] <;> simp +contextual [leftFlag]

end YM.Integration.PhysicalForestCenter
