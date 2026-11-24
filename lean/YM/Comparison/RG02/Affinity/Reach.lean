import YM.Comparison.RG02.Affinity.Vibe
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

open Gaussian PertExtension.Series
open scoped Topology
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {Q : Gaussian.Table I} {g : ℝ}
  {f : House X I →ℝ} {l : Hot R→ℕ} {F : Hot R→House X I→ℂ}
local notation "E"=>House X I

omit [DecidableEq I] in
lemma funded (hf : GradeAt 2 f) (hF : ∀ s, GradeAt (l s) (F s)) : Assembly.Admissible l F f :=
   ⟨⟨hf.smooth.of_le le_top, Buy.begins hf,fun y=> hf.jet_z y one_lt_two⟩,
      fun i=> ⟨(hF i).smooth.of_le le_top,fun _ h v=> (hF i).jet_z v h⟩⟩
-- lower slope & B asserted via `Vibe`. all drivers with t powers supported.
variable (R) (x : X) (S : Vibe X I)

def reach (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] : (I→ℝ) →ₗ[ℝ] House X I := (LinearMap.inr ℝ _ _).comp (LinearMap.inr ℝ X _)
-- `season`: same symbol AUTHENTIC for either radial price

def season (v:I→ℝ) : House X I := Assembly.translate (1,x,0) (reach X) v
omit [DecidableEq I] in
@[simp] lemma facing (v:I→ℝ) : season x v=(1,x,v) := by
   unfold season Assembly.translate reach
   apply Prod.ext (by exact add_zero _)
   exact Prod.ext (add_zero _) (zero_add _)
omit [DecidableEq I] in
@[fun_prop] lemma season_cont : Continuous (season (I:=I) x) := by rw [show season (I:=I) x=fun v=>(1,x,v) from funext (facing x)]; fun_prop

namespace Vibe

def shifter (g:ℝ) := g⁻¹ • S.m (g,g • x)
def basis (g:ℝ) := S.B (g,g • x)
def outreach (g:ℝ) (v:I→ℝ) := shifter x S g + (basis x S g) *ᵥ v
@[fun_prop] lemma continuous_outreach (g:ℝ) : Continuous (outreach x S g) := by unfold outreach; exact continuous_const.add ((basis x S g).mulVecLin.continuous_on_pi)
lemma emblem (v:I→ℝ) (hg : g≠0) : S.effect (g • season x v)=g • season x (outreach x S g v) := by
  simp_rw [facing]; unfold effect; refine Prod.ext rfl (Prod.ext rfl ?_)
  change S.m (g*(1:ℝ),g•x)+ S.B (g*(1:ℝ),g•x) *ᵥ (g • v)=g • (outreach x S g v)
  rw [mul_one, outreach,shifter,basis, Matrix.mulVec_smul,smul_add, smul_smul,mul_inv_cancel₀ hg,one_smul]
lemma enacted (v:I→ℝ) (hg : g≠0) (hf : Ray Q f) : Radial.higher (S.price f) g (season x v)=
    Radial.higher f g (season x (outreach x S g v)) + force Q v/2 - force Q (outreach x S g v)/2 + Real.log (basis x S g).det := by
   unfold Radial.higher; simp_rw [← Assembly.jet_eq]; rw [price_starts _ hf.root]; simp only [ price,Pi.sub_apply, Function.comp_apply, emblem x S _ hg]
   unfold logDet; simp_rw [facing]; nth_rw 1 [hf.quadratic x v]; nth_rw 1 [hf.quadratic x (outreach x S g v)]; unfold basis
   rw [show g • ((1,x,v):E)=(g,g •x,g • v) from Prod.ext (mul_one g) rfl]; dsimp only; field_simp; ring
lemma marks (v:I→ℝ) (hg : g≠0) : smoothMark (R:=R) l (fun i=> F i ∘ S.effect) g (season x v) = smoothMark l F g (season x (outreach x S g v)) := by unfold smoothMark Assembly.divided; simp_rw [Function.comp_apply,emblem x S _ hg]
variable [Fintype V]
lemma scene (hg : g≠0) (hB : 0<(basis x S g).det) (hf : Ray Q f) (v : I→ℝ):
   Assembly.numeric (R:=R) l (fun i=> F i ∘ S.effect) (S.price f) g (season x v) = account Q (basis x S g) (shifter x S g) (Assembly.numeric l F f g ∘ season x) v := by
   unfold account Assembly.numeric
   rw [marks _ x S v hg, Function.comp_apply, enacted x S v hg hf,toll]
   change _= Complex.ofReal ((basis x S g).det*Real.exp (force Q v/2-force Q (outreach x S g v)/2)) •
         (Poly.bead R ↑(Real.exp (Radial.higher f g (season x (outreach x S g v))))* Poly.pass (smoothMark l F g (season x (outreach x S g v))))
   rw [Poly.product_bead,Poly.product_bead, smul_smul,← Complex.ofReal_mul, ← show Radial.higher f g (season x (outreach x S g v))+(force Q v/2-force Q (outreach x S g v)/2) = _ from (add_sub_assoc ..).symm]
   rw [Real.exp_add, Real.exp_add,Real.exp_log hB]; congr 2; ring
-- exact convolution along real aperture event
lemma within (hg : g≠0) (hB : 0<(basis x S g).det) (hf : Ray Q f) (hq : Q.PosDef) (A : Set (I→ℝ)) :
    let f1 : Lit R (I→ℝ) := A.indicator (Assembly.numeric l F f g ∘ season x)
    let f2 : Lit R (I→ℝ) := (outreach x S g ⁻¹' A).indicator (Assembly.numeric (R:=R) l (fun i=> F i ∘ S.effect) (S.price f) g ∘ season x)
    (Good (cloud Q) f1 ↔ Good (cloud Q) f2) ∧ charge (cloud Q) f1=charge (cloud Q) f2 := by
   intro a b; rw [show b=account Q (basis x S g) (shifter x S g) a by
      exact (
         (congrArg (_root_.Set.indicator (outreach x S g ⁻¹' A)) (funext (scene R x S (l:=l) (F:=F) hg hB hf)) ).trans (on_cut ..))]
   have h:=at_account Q (basis x S g) (shifter x S g) hB hq a; exact ⟨h.1,h.2.symm⟩
end Vibe
end YM.Comparison.RG02.Affinity
