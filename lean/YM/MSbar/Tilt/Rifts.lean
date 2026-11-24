import YM.MSbar.Tilt.Files
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Positions (Primary n G)
local notation "V"=> G.Color
variable (z:Site n→G.Color) (x:Positions (Primary n G))
variable {R B C D E t c:ℝ}
local notation "L"=> tint G (Body 1 n)
noncomputable def hung (F:Rep G n)(f:Nesting G n)(t:ℝ)(p:ℕ)(ρ:Site n→ G.Color) (x:Positions (Primary n G)) := fderiv ℝ (ore F f t p) x (speedsK ρ (t • x))
variable (F: Rep G n)(f:Nesting G n)(x' :Positions (Primary n G))(p:ℕ)(V':Finset (Body 1 n))
variable {A b B U a:ℝ}{α:ℝ→ Config G n→ℝ}
variable (hf:Trend α f F.path F.clip p)
local notation "q"=> hung F f t p z
local notation "X"=> {x: Positions (Primary n G)| ‖tint G _ x‖ ≤ A}
variable (ha: ∀ i≤p,Stone G i 2 E b)(hr:t >0)(hr':t ≤1)
local notation "f!"=> fun i=> atlas f p i F.path F.clip
variable (hQ:∀ i≤p,∀ x:Positions (Primary n G), ‖tint G _ x‖ ≤ A → ∀ j:Primary n G, |fderiv ℝ (atlas f p i F.path F.clip) x (bolt j)| ≤ B ∧ ∑ u:Primary n G, |buoy (atlas f p i F.path F.clip) x [u,j]| ≤ B)
variable (he: t*A<E) (hp: 1≤A)
local notation "P!"=> costP
include hQ hf ha he hr hr' hp
noncomputable def coal (G:Gauge)(p:ℕ)(v C t A B:ℝ) := ∑ i∈Finset.range (p+1), t^i * (fCost v t A (p-i)* C*((G.lieDim+1:ℕ)*B))
lemma runZ(hx:‖tint G _ x‖ ≤ A)(hz:∀ i:Body 1 n, ‖ran z i‖ ≤ U) : DifferentiableAt ℝ (hung F f t p z) x ∧ ∀ i:Primary n G, |fderiv ℝ (hung F f t p z) x (bolt i)| ≤ coal G p b U t A B:=by
    let g(i) := costP (f! i) (sift z (p-i) t); let S:=Finset.range (p+1);
    have hK(j :Body 1 n): ‖tint G _ (t • x) j‖<E:=by rw [map_smul, Pi.smul_apply,norm_smul,Real.norm_of_nonneg hr.le]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans hx) hr.le) he
    have he': HasFDerivAt (q) (∑ i∈Finset.range (p+1), t^i • fderiv ℝ (g i) x) x:=by
         have hg:(q)= (fun y=> ∑ i∈ S,t^i*g i y):=funext (timbre z F f p hf t); rw [hg]; apply HasFDerivAt.fun_sum ..; intro i hi; have hA(i):ContDiffAt ℝ 2 (g i) x:= ((vent ..).contDiffAt (x:=x)|>.fderiv_right (m:=2) (by simp)).clm_apply (comb z (p-i) x (ha _ (by omega)) t hK); exact ((hA i).differentiableAt (by simp)|>.hasFDerivAt).const_smul (t^i)
    refine ⟨he'.differentiableAt,fun i=>?_⟩; rw [he'.fderiv,_root_.sum_apply]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j hj=>?_); have ht := Nat.lt_succ_iff.mp (mem_range.mp hj); have hu:= hQ j ht x hx; change |t^j * fderiv ℝ (g j) x _| ≤ _; rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ t^j)]; exact mul_le_mul_of_nonneg_left (warrant z x i (p-j) hr hr' (ha _ (by omega)) he hx hp hz ((vent ..).contDiffAt.of_le le_top) (fun i=> hu i|>.1) (fun i=>hu i|>.2)) (by positivity)
variable (h:Guide G C D) (hh: t*R<C)(hk:t*R<E)(hX:‖tint G _ x‖≤R)(hY:‖tint G _ x'‖≤R) (hz:∀ i:Body 1 n, ‖ran z i‖ ≤ R)
include h hh hX hY hz hk
local notation "u₀"=>reset z t
lemma tap (hG:∀ i:Body 1 n,i∉V'→ tint G _ x i=tint G _ x' i) (hs:∀ s,0≤ s → s≤1 → ‖tint G _ (reset z t x s)‖ ≤ A ∧ ‖tint G _ (reset z t x' s)‖ ≤ A) (hB:0≤B):
    let H:= ore F f t p
    |(H (reset z t x' 1)-H x')-(H (reset z t x 1)-H x)| ≤ coal G p b R t A B * ((V'.card *G.lieDim:ℕ)*(A+A)):=by
    intro H; let g(s:ℝ):=H (u₀ x' s)-H (u₀ x s); let Y₁:= reset z t x'; let Y:=reset z t x; let w:= coal G p b R t A B; have hR:0 ≤ R:=(norm_nonneg _).trans hX; have hC : 0 ≤ coal G p b R t A B :=Finset.sum_nonneg fun i _=>by unfold fCost; have hb:0≤b:=(ha 0 (by omega)).positive; positivity
    let L':= L; let H':=L'.toContinuousLinearMap; let Z:= X; have hV:Convex ℝ X:=by
        have hx' : Convex ℝ (Metric.closedBall (0: Exterior.fieldDir G n 1) A):=convex_closedBall ..; rw [show X= (⇑H' ⁻¹' Metric.closedBall 0 A) from ?_]; · exact hx'.linear_preimage H'.toLinearMap
        ext i; simp [H', L']
    have hd:Guide G C D:=h; have hb:Beam G E:=(ha 0 (by omega)).beam; have ht : (H (Y₁ 1)-H x')-(H (Y 1)-H x)=g 1-g 0 :=by unfold g Y Y₁; rw [wake z x h hr hX hz hh hb hk, wake z x' h hr hY hz hh hb hk]; ring
    rw [ht]; refine Tilt.mean _ (fun v=> q (Y₁ v)- q (Y v)) ?_; intro i hi; obtain ⟨hu,hU⟩:=hs i hi.1 hi.2; have hp':|i|≤ 1:=(abs_of_nonneg hi.1).trans_le hi.2; have hD(z':Positions (Primary n G))(he':‖L z'‖ ≤ R)(hi':‖L (reset z t z' i)‖ ≤ A) : HasDerivAt (H ∘ u₀ z') (q (u₀ z' i)) i:=by
        apply (((Aqua.pure ..).differentiable (by simp) (u₀ z' i)).hasFDerivAt.comp_hasDerivAt i (Tilt.vital z z' h hr he' hz hh hb hk i hp' ?_)); intro j; rw [map_smul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg hr.le]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans hi') hr.le) he
    refine ⟨(hD _ hY hU).sub (hD _ hX hu),?_⟩
    have hS(U W: K)(d:ℝ) (h:‖L U‖≤A)(hz:‖L W‖≤A)(hf:∀ i∈Finset.univ \ (V' ×ˢ (Finset.univ:Finset G.ColorIndex)), U i= W i): moves U W≤ ((V'.card*G.lieDim:ℕ)*(A+A)):=by
        let K':=V' ×ˢ (Finset.univ:Finset G.ColorIndex); have hP(x:K)(hx:‖L x‖ ≤ A)(j:Primary n G): |x j| ≤ A:=le_trans (show ‖L x j.1 j.2‖≤ ‖L x j.1‖ from PiLp.norm_apply_le _ _) ((norm_le_pi_norm _ _).trans hx)
        unfold moves; rw [← Finset.sum_subset (s₁:=K') (Finset.subset_univ _) (fun x hi ht=>show |W x-U x| = (0:ℝ) from by rw [hf x (Finset.mem_sdiff.mpr ⟨hi,ht⟩), sub_self,abs_zero])]; refine (Finset.sum_le_sum (fun i _=> (abs_sub _ _).trans (add_le_add (hP _ hz i) (hP _ h i)))).trans_eq ?_; unfold K'; rw [Finset.sum_const, card_product,card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply (Tilt.allV (q) Z hV (fun y hy=>runZ z y F f p hf ha hr hr' hQ he hp hy hz|>.1) (fun y hy=>runZ z y F f p hf ha hr hr' hQ he hp hy hz|>.2) hu hU).trans; refine mul_le_mul_of_nonneg_left (hS _ _ 0 hu hU (fun p hi=>?_)) hC
    have hx:p.1∉V':=by intro hg; apply (Finset.mem_sdiff.mp hi).2; exact Finset.mem_product.mpr ⟨hg,mem_univ _⟩
    unfold reset; rw [Pi.smul_apply, Pi.smul_apply]; congr 1; apply congrArg (fun v:G.Color=>v p.2) (show Native.Chart.head G (ran z p.1) (i*t,L (t •x) p.1)=Native.Chart.head G (ran z p.1) (i*t,L (t •x') p.1) from (by rw [map_smul,map_smul, Pi.smul_apply,Pi.smul_apply,hG p.1 hx]))
end YM.MSbar.Tilt
