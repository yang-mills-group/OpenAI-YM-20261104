import YM.Comparison.RG02.Affinity.Gaussian
import YM.Push.LOOP_COEFFICIENT.LogDet
/-!
# Field-dependent linear changes of the full Gaussian axis

At the analytical-interior model, shift by an arbitrary analytic `m`: grade 2 after
 the prior linear-stationary shift has already been included. `B(0)=I`; no pullback along
 insertion markers (would risk dividing on a diff tangent measure). Positive det at
 zero, paid at other points by hypothesis. Overall exponent includes -t^2 log(det) with
 relative-Haar still in the previous frame. At this real leg, no actual beta changed,
 only `K.coefficient` comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Gaussian PertExtension.Series Work.F05

abbrev House (X I : Type) := ℝ× X × (I→ℝ)
abbrev Regulator (X : Type) := ℝ×X

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "M"=>Matrix I I ℝ
local notation "E"=> House X I

-- strain equipment lives across `F.g`. defining incidences in counting convention even if one
-- packages/change uses FieldDir at actual geometry.
structure Ray (Q : Gaussian.Table I) (f : House X I → ℝ) : Prop where
   root : Assembly.GradeAt 2 f
   quadratic (x : X) (v : I→ℝ) : Assembly.jet f 2 (1,x,v)=Assembly.jet f 2 (1,x,0)+ Gaussian.force Q v/2

namespace Buy
section
variable {W' W : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [NormedAddCommGroup W] [NormedSpace ℝ W] {g:W'→W} (hg:Assembly.GradeAt 2 g)
include hg
lemma begins : g 0=0 := by simpa only [Assembly.jet_zero] using hg.jet_z 0 (by omega : 0<2)
lemma second : fderiv ℝ g 0=0 := by
   ext v; have h:=hg.jet_z v (by omega : 1<2); unfold Assembly.jet at h; simpa [iteratedFDeriv_one_apply] using h
omit hg in
lemma deuce (g:W'→W) (h : ContDiffAt ℝ ω g 0) (hc : g 0=0) (he : fderiv ℝ g 0=0): Assembly.GradeAt 2 g := by
   refine ⟨h,fun i hi=>?_⟩; interval_cases i
   · exact (GradeAt.anchored h hc).vanish _ (by decide)
   ext1 v; rw [iteratedFDeriv_one_apply,he]; rfl
end
end Buy

structure Vibe (X I : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype I] [DecidableEq I] where
   m : Regulator X → (I→ℝ)
   B : Regulator X → Matrix I I ℝ
   roots : Assembly.GradeAt 2 m
   smooth : ContDiffAt ℝ ω B 0
   identity : B 0=1

namespace Vibe

variable (S : Vibe X I)
private def lamp : House X I →L[ℝ] Regulator X := (ContinuousLinearMap.fst ℝ ℝ _).prod ((ContinuousLinearMap.fst ℝ X _).comp (ContinuousLinearMap.snd ℝ _ _))
private def wire : House X I→L[ℝ](I→ℝ) := (ContinuousLinearMap.snd ℝ X _).comp (ContinuousLinearMap.snd ℝ _ _)
private def send (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] : (I→ℝ)→L[ℝ]House X I := (ContinuousLinearMap.inr ℝ _ _).comp (ContinuousLinearMap.inr ℝ X _)

private def blendCLM : Matrix I I ℝ →L[ℝ] (I→ℝ) →L[ℝ] (I→ℝ) :=
  ({toFun := fun J=> J.mulVecLin.toContinuousLinearMap
    map_add':=fun A B=> by ext1 v; exact Matrix.add_mulVec A B v
    map_smul':=fun A B=> by ext1 v; exact Matrix.smul_mulVec .. } : M →ₗ[ℝ] (I→ℝ) →L[ℝ] (I→ℝ)).toContinuousLinearMap

def effect (a : E) : E := (a.1,a.2.1,S.m (a.1,a.2.1)+ S.B (a.1,a.2.1) *ᵥ a.2.2)
def reverse (a : E) : E := (a.1,a.2.1, (S.B (a.1,a.2.1))⁻¹ *ᵥ (a.2.2 - S.m (a.1,a.2.1)))

lemma resets (a : E) (h : IsUnit (S.B (a.1,a.2.1)).det) : S.reverse (S.effect a)=a := by
  simp [reverse,effect,Matrix.mulVec_mulVec, (S.B _).nonsing_inv_mul h]

private lemma starts : GradeAt 2 (S.effect-id) := by
  let f : E→ M := S.B ∘ lamp
  have hF : ContDiffAt ℝ ω f 0 := S.smooth.comp (f:=lamp) (0:E) (lamp (X:=X) (I:=I)).contDiff.contDiffAt
  have h0 : f 0=1 := S.identity
  have hm : GradeAt 1 (f-fun _:E=>(1:M)) := GradeAt.anchored (hF.sub contDiffAt_const) (by simp only [Pi.sub_apply,h0,sub_self])
  have hv := GradeAt.combo blendCLM hm (GradeAt.anchored (wire (X:=X) (I:=I)).contDiff.contDiffAt (wire (X:=X) (I:=I)).map_zero)
  have hw := (S.roots.coarse (g:=lamp) (lamp (X:=X) (I:=I)).contDiff.contDiffAt (lamp (X:=X) (I:=I)).map_zero).add hv
  refine (GradeAt.linear_contact (send X) hw).depends (Eventually.of_forall fun (y : E) => ?_)
  change (0, 0,S.m _+(S.B _-1) *ᵥ y.2.2)=S.effect y - y
  rw [Matrix.sub_mulVec,Matrix.one_mulVec]; unfold effect
  apply Prod.ext (by simp); apply Prod.ext (by simp); simp [add_sub_assoc,lamp]

lemma base : S.effect 0=0 := by simpa using Buy.begins S.starts
lemma back : S.reverse 0=0 := by unfold reverse; simp only [Prod.fst_zero,Prod.snd_zero]; rw [show ((0:ℝ),(0:X))=0 from rfl,S.identity,inv_one,Buy.begins S.roots,sub_zero,Matrix.one_mulVec]; rfl

lemma no_jets : fderiv ℝ S.effect 0=ContinuousLinearMap.id ℝ E ∧ ContDiffAt ℝ ω S.effect 0 := by
   let g:=S.effect-id
   have hv : GradeAt 2 g := S.starts
   have he : S.effect=g+id:= (sub_add_cancel S.effect id).symm
   refine ⟨?_, he ▸ hv.smooth.add contDiffAt_id⟩
   rw [he,fderiv_add (hv.smooth.differentiableAt (by simp)) differentiableAt_id,Buy.second hv,fderiv_id,zero_add]
lemma continuous_back : ContDiffAt ℝ ω S.reverse 0 := by
   let E' : E→ M := S.B ∘ lamp
   let F : E→ M:=fun a=> (E' a)⁻¹
   have hE : ContDiffAt ℝ ω E' 0 := S.smooth.comp (f:=lamp) (0:E) (lamp (X:=X) (I:=I)).contDiff.contDiffAt
   have hV : ContDiffAt ℝ ω F 0 := (YM.Push.Loops.inv_contDiffAt (E' 0) (by rw [show E' 0=1 from S.identity, Matrix.det_one]; simp)).comp 0 hE
   have hh : ContDiffAt ℝ ω (fun a:E=> blendCLM (F a) (a.2.2-S.m (a.1,a.2.1))) 0 := ((blendCLM (I:=I)).contDiff.contDiffAt.comp 0 hV).clm_apply (((wire (X:=X) (I:=I)).contDiff.contDiffAt : ContDiffAt ℝ ω (wire (X:=X) (I:=I)) 0).sub (S.roots.smooth.comp (f:=lamp) (0:E) (lamp (X:=X) (I:=I)).contDiff.contDiffAt))
   exact contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk hh)

def logDet (z : E) := z.1^2 * Real.log (S.B (z.1,z.2.1)).det
def price (f : E→ℝ) := f ∘ S.effect-S.logDet
lemma taxes : Assembly.GradeAt 3 S.logDet := by
   have ht : GradeAt 2 (fun z:E=> z.1^2):= GradeAt.shifts _ contDiffAt_fst rfl 2
   have ho : ContDiffAt ℝ ω (fun z:E=>Real.log (S.B (z.1,z.2.1)).det) 0 := (YM.Push.Loops.logdet_contDiff S.smooth (by rw [S.identity, Matrix.det_one]; simp)).comp (f:=lamp) (0:E) (lamp (X:=X) (I:=I)).contDiff.contDiffAt
   exact ht.mul (GradeAt.anchored ho (by simp [show ((0:ℝ),(0:X))=0 from rfl, S.identity]))

variable {Q : Gaussian.Table I} {f : House X I →ℝ}
lemma price_starts (h : GradeAt 2 f) (a:E) : Assembly.jet (S.price f) 2 a= Assembly.jet f 2 a := by
  have hp : fderiv ℝ f (S.effect 0)=0 := S.base.symm ▸ Buy.second h
  have hF : ContDiffAt ℝ ω f (S.effect 0) := S.base.symm ▸ h.smooth
  have hd := S.taxes; unfold price Assembly.jet;
  rw [iteratedFDeriv_sub_apply ((hF.comp _ S.no_jets.2).of_le le_top) (hd.smooth.of_le le_top), hd.vanish _ (by decide), sub_zero]
  rw [show (fun _:Fin 2=>a)=![a,a] by funext i; fin_cases i <;> rfl, ← bend_apply,← bend_apply, bend_comp_stationary hF S.no_jets.2 hp,S.base,S.no_jets.1]; rfl
lemma prices (h : Ray Q f) : Ray Q (S.price f) := by
  refine ⟨(h.root.coarse S.no_jets.2 S.base).sub (S.taxes.lower (by omega)),fun x v=>?_⟩
  simp_rw [price_starts S h.root]; exact h.quadratic x v

end Vibe
end YM.Comparison.RG02.Affinity
