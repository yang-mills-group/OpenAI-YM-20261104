import YM.MSbar.Rolling.Light
import YM.MSbar.Sat.Pitch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set Cacao
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
open Push.Uniform
variable {ι σ:Type} [Fintype ι][Fintype σ] [DecidableEq σ]
-- native lexicase dot product, not normPi^2.
local notation "X"=> Positions ι
local notation "Z"=> Positions σ
local notation "T"=> Positions (ι⊕σ)
local notation "∆"=> fderiv ℝ
noncomputable abbrev rim {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] (f:E→F):= ∆ (∆ f) 0
local notation "O"=> (0:T)
variable {f: Positions (ι⊕σ) → ℝ}{p: Positions ι → Positions σ}
local notation "K"=> Push.Uniform.block f O
local notation "µ₀"=> Slope f
variable (h:ContDiffAt ℝ ω f 0) (x:Positions (ι⊕σ))
private lemma zeroC : meetVar (0:Positions ι) (0:Positions σ)=(0:Positions (ι⊕σ)):=map_zero (partSpace ι σ).symm
include h
-- Counting matrix. avoids active DecidableEq orth.Mold
lemma postS(v: Z) : rim f x (meetVar (0:X) v) = dotProduct v (∆ (Slope f) O x) := by
    let P:=rim f x; rw [show meetVar (0:X) v=lowerCol v from rfl]; change ((P.comp lowerCol) v) = _; rw [by_row]; apply Finset.sum_congr rfl; intro i _; simp only [smul_eq_mul,ContinuousLinearMap.comp_apply]; apply congr_arg
    let A':= fderiv ℝ f; let Q : (T→L[ℝ] ℝ) →L[ℝ] ℝ:= ContinuousLinearMap.apply ℝ ℝ (bolt (Sum.inr i)) -- check
    let q : Z →L[ℝ] ℝ := ContinuousLinearMap.proj i
    let Y:=µ₀; have hh : Q ∘ A'= q ∘ Y:=by
        ext1 x; change ∆ f x _= _; unfold q Y; change _=Slope f x i; unfold Slope entry; rw [iteratedFDeriv_one_apply];rfl
    have hu : DifferentiableAt ℝ Y O:=(zeroC (ι:=ι) (σ:=σ)) ▸ (slope_block (f:=f) (x:=0) (v:=0) ((zeroC (ι:=ι) (σ:=σ)).symm ▸ h)).1.differentiableAt (by simp)
    have hv : DifferentiableAt ℝ A' O:=(h.fderiv_right (m:=1) (by simp)).differentiableAt (by simp); have he := congr_arg (fun f:T→ℝ=> ∆ f O) hh; rw [fderiv_comp _ Q.differentiableAt hv,fderiv_comp _ q.differentiableAt hu,Q.fderiv,q.fderiv] at he; rw [lower_bolt]; exact congr_arg (fun f:T→L[ℝ]ℝ=> f x) he
omit x
lemma at_post (v:Positions σ) : ∆ (Slope f) O (meetVar (0:X) v) = K *ᵥ v:=by
   have hz : meetVar (0:X) (0:Z)=(0:T) := zeroC
   have hh:=slope_block (hz.symm ▸ h: ContDiffAt ℝ ω f (meetVar (0:X) (0:Z)))
   have he:= (hh.1.differentiableAt (by simp)).hasFDerivAt.comp 0 (meet_derivative (0:X) (0:Z)); have hu:=hh.2 v; rw [he.fderiv,hz] at hu; exact hu
lemma portrait {K₀: Matrix σ σ ℝ}(hK:K₀=Push.Uniform.block f 0)(he : ∀ v:Positions σ,v≠0 → 0 < rim f (meetVar (0:X) v) (meetVar (0:X) v)): K₀.PosDef:=by
    subst K₀; refine Matrix.PosDef.of_dotProduct_mulVec_pos (block_hermitian h) (fun i hi=>?_); have hx:=he i hi; rw [postS h,at_post h] at hx; simpa only [star_trivial] using hx
-- invest the stationary Hess joint. `slopeUnion`
variable (h0:p 0=0)(hp:ContDiffAt ℝ ω p 0)(hd:∀ᶠ x:Positions ι in 𝓝 0,Slope f (meetVar x (p x))=0)
-- L.Def should exactly equiv.P. Estimate compare.Solver
include hp h0 hd
lemma pulse1 (v:Positions ι): ∆ (Slope f) O (meetVar v ((∆ p 0) v))=0:=by
    let L:=∆ p (0:X); let w(x:X):=meetVar x (p x); let D: X→L[ℝ] T:=(partSpace ι σ).symm.toContinuousLinearMap.comp ((ContinuousLinearMap.id ..).prod L); have hh:HasFDerivAt w D 0:=(partSpace ι σ).symm.hasFDerivAt.comp _ ((hasFDerivAt_id _).prodMk (hp.differentiableAt (by simp)).hasFDerivAt)
    have hv : w 0=O:=by unfold w; rw [h0];exact zeroC
    let A:=µ₀; have he : DifferentiableAt ℝ A (w 0):=by rw [hv,←zeroC (σ:=σ) (ι:=ι)]; exact (slope_block (x:=(0:X)) (v:=(0:Z)) ((zeroC (σ:=σ) (ι:=ι)).symm ▸ h)).1.differentiableAt (by simp)
    have hz := he.hasFDerivAt.comp 0 hh
    have hx:A ∘ w=ᶠ[𝓝 (0:X)] (fun _=>0):=hd
    have hh' := (hz.congr_of_eventuallyEq hx.symm).unique (hasFDerivAt_const ..); rw [hv] at hh'; exact congr_arg (fun i:X→L[ℝ]Z=>i v) hh' -- edit domain
lemma pulseK (x:Positions ι)(hK:(Push.Uniform.block f 0).PosDef): ∆ p 0 x=vest f x:=by
    let A: X→L[ℝ] Z:=∆ p 0
    let U: Matrix σ σ ℝ:=K
    have hc:=hK.det_pos
    have he:=pulse1 h h0 hp hd x; rw [meet_columns,map_add,at_post h] at he
    have hh : -((U⁻¹ : Matrix σ σ ℝ) *ᵥ ∆ µ₀ O (meetVar x (0:Z)))=A x:= by
        rw [eq_neg_of_add_eq_zero_left he,mulVec_neg,mulVec_mulVec, Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hc.ne'),one_mulVec, neg_neg] -- U defeq but rewrite
    exact hh.symm
lemma pulse2 (x:Positions ι) (u:Positions σ) : let v:= ∆ p 0 x
    rim f (meetVar x (v+u)) (meetVar x (v+u)) = rim f (meetVar x v) (meetVar x v) + dotProduct u (Push.Uniform.block f 0 *ᵥ u):=by
    intro v; let G:=meetVar x v; let H:=meetVar (0:X) u; have hk: rim f H H= dotProduct u (K*ᵥ u):= by unfold H; rw [postS h,at_post h]
    have hg : rim f G H=0:=by unfold H; rw [postS h,show ∆ µ₀ O G=0 from pulse1 h h0 hp hd x,dotProduct_zero]
    rw [show meetVar x (v+u)=G+H from (by unfold G H meetVar; rw [← map_add,Prod.mk_add_mk,add_zero]), map_add, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, hk, show rim f H G=rim f G H from h.isSymmSndFDerivAt_of_omega _ _, hg]; simp [G]
end YM.MSbar.Rolling
