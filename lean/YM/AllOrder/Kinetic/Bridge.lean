import YM.AllOrder.Kinetic.Hill
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
variable (e:rule α n≃L[ℝ]X)(v:rule β n≃L[ℝ]Y)
local notation "L"=> (α⊕β)
local notation "I"=> Leaf n L
local notation "E"=> X×Y
local notation "I'"=> Leaf n β
open MeasureTheory Work.F08
variable (A:X × Y→ℝ)(ρ:X→Y) (h:Steered A ρ) (U:Stalk (α⊕β) (α⊕β)) (V:Stalk β β)
local notation "A₀"=> mail e v A
local notation "B"=> pulse e v A
local notation "J"=> posture e v
local notation "F"=> faces v
set_option quotPrecheck false
local notation "W"=> castle A ρ h
-- annihilate ratio
variable [DecidableEq α][DecidableEq β]
variable (ht:direct V n=(pulse e v A)⁻¹) (hM:direct U n=mail e v A)
def turn (f:rule (α⊕β) n) := know (applyM U V) n f
abbrev KΞ := fderiv ℝ ρ 0
include h ht hM
lemma arranged (hU:Belt U a C)(hV:Belt V a D)(ha:0≤a)(h0:0≤D)(x:rule α n)(y:rule β n) : posture e v (turn U V (mingle x y))=(e x,KΞ ρ (e x)+v y) := by
 let s:=e x; let g:=wagon x A₀; let w:= v.symm (fderiv ℝ ρ 0 s); have hp:B*ᵥ w= -g:= funext fun i=> joints_turn e v A ρ h x i; unfold turn; rw [(rentM U V x y ha hU hV h0).2, suite, hM]; change (s,v (y-(direct V n *ᵥ g))) =_; rw [ht]; let A' : Ink.BoardL n β β:= Matrix.of fun i j=> rowM (W) F j i; have hA:=spring_inv e v A ρ h; have hb : B*A'=1:=hA; have hh : A'*ᵥ (-g)=w:= by rw [←hp,mulVec_mulVec,mul_eq_one_comm.mp hb, Matrix.one_mulVec]
 rw [Matrix.inv_eq_right_inv hb,sub_eq_add_neg,← Matrix.mulVec_neg,hh,map_add]; exact Prod.ext rfl (by change v y + v (v.symm _) = _ + v y; rw [ContinuousLinearEquiv.apply_symm_apply]; abel)

omit h hM ht [DecidableEq α]
abbrev peg₀ (i: I') := Primitives.TwoWave.peg α i
local notation "P'"=> (@peg₀ n α β) -- arguments? print
omit [DecidableEq β] in
lemma d_j (f:X×Y→ℝ) (H:Plausible f)(i:Leaf n β) : dab (peg₀ (α:=α) i) (f ∘ posture e v)= diff' (vec (X:=X) F i) f ∘ posture e v:= by
  funext x; unfold dab diff'; rw [fderiv_comp x (H.smooth.differentiable (by simp) _) (ContinuousLinearEquiv.differentiableAt ..), ContinuousLinearEquiv.fderiv]; exact congr_arg (fderiv ℝ f _) (song e v i)
variable [MeasurableSpace Y][BorelSpace Y] (μ:Measure Y)[μ.IsAddHaarMeasure]
include h ht
local notation "V'"=> expand V α
lemma positive (i j:Leaf n β): direct (expand V α) n (peg₀ (α:=α) i) (peg₀ (α:=α) j)=rowM (W) F i j:= by change direct V n i j=_; rw [ht,spring e v A ρ h]
-- commute K operator with basis
omit ht h in
lemma thin (i:Leaf n L)(j:Leaf n α): direct (V') n i (lead β j) = 0 ∧ direct (V') n (lead β j) i=0:= by rcases i with ⟨x,i|j⟩ <;> simp [expand,direct,lead,Primitives.TwoWave.up]
lemma lighting_p {f:X×Y→ℝ}(hv:Plausible f) : flicker (expand V α) n (f ∘ J)= infinity (W) (F) f ∘ J := by
   ext1 x; rw [flicker,Finset.sum_apply,cut_sum]; let K:= V'; let X':= J x;
   have hz(i:Leaf n α)(j:I): direct K n (lead β i) j=0:=(thin V j i).2
   have hs(i:I)(j:Leaf n α): direct K n i (lead β j)=0:=(thin V i j).1
   simp_rw [Finset.sum_apply, Pi.smul_apply]; change (∑ i:Leaf n α,∑ j:I,direct K n (lead β i) j • _)+(∑ j:Leaf n β,∑ l:I,direct K n (peg₀ (α:=α) j) l • _) =_
   simp_rw [hz,zero_smul,Finset.sum_const_zero]; rw [zero_add,Function.comp_apply,duplex,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [cut_sum, Finset.sum_apply]; simp_rw [hs,zero_smul,Finset.sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro j _; rw [show direct K n _ _=_ from positive e v A ρ h V ht i j,Pi.smul_apply, d_j e v f hv i, d_j e v _ (hv.ds _) j]; rfl
end YM.AllOrder.Kinetic
