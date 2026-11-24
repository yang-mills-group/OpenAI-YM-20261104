import YM.FormalBulk08.Hay.Wagon

/-! Mesh Fourier comparison to aim fixed position. Polynomial loss in n OK here;
interfaces exponentially converging from `FiniteBound`, not assuming bulk coeff. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Matrix
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{n:Side}{w:ℝ}

def torch (G:Gauge)(n:Side)(i b: Lines G n 1)(p: TypeFace 1)(j:hue G): ℂ :=
    if b.2=(p,j) then ((n.val:ℂ)^4)⁻¹ * (star (rotations n (Loc G 1))) b i else 0
lemma torch_spark (i b: Lines G n 1)(p: TypeFace 1)(j:hue G):‖torch G n i b p j‖ ≤1:= by
   unfold torch;split;swap;· simp
   rw [norm_mul,norm_inv, Matrix.star_eq_conjTranspose]; simp only [Matrix.conjTranspose_apply,norm_star]; apply mul_le_one₀ _ (norm_nonneg _) _
   · apply inv_le_one_of_one_le₀; rw [norm_pow]; refine one_le_pow₀ ?_; rw [Complex.norm_natCast]; exact_mod_cast Nat.succ_le_of_lt n.pos
   unfold rotations; rw [Matrix.of_apply];split
   next a=> simp [cell,Laurent.mode_real (mon b.1) _ (real_frequency b.1)]
   simp
lemma into_cell (i: Lines G n 1): dotI i= ∑ x:Lines G n 1, pew x.1 (torch G n i x):= by
   let R:= rotations n (Loc G 1); let q:ℂ:=(n.val:ℂ)^4; have h:q≠0:= pow_ne_zero 4 (side_ne _)
   ext1 j; let d:=axes (dotI i); let f x:= q⁻¹*(star R) x i; have he: d j= ∑ x:Lines G n 1,R j x*f x:= by
      have ht:=congr_fun (congr_fun (rotations_gram n (Loc G 1)) j) i; simp only [ Matrix.smul_apply, Matrix.mul_apply] at ht
      unfold f; simp_rw [mul_left_comm _ q⁻¹,← Finset.mul_sum]; unfold R;rw [ht,smul_eq_mul, inv_mul_cancel_left₀ h]; by_cases hp:i=j <;> simp [d,dotI,axes,hp, Matrix.one_apply,Ne.symm]
   rw [Finset.sum_apply]; have ht:=congr_arg Complex.re he; rw [Complex.re_sum] at ht; refine Eq.trans ht (Finset.sum_congr rfl fun k _=>?_)
   congr 1; unfold R rotations; rw [of_apply]; by_cases hh:k.2=j.2 <;> simp [f,torch,q,hh,R,Ne.symm] -- test

def skyL (G:Gauge)(n:Side):ℝ := ((Fintype.card (Lines G n 1) :ℝ)^2)
lemma sky_value (G:Gauge)(n:Side): skyL G n= (((n.val:ℝ)^4)^2)*Fintype.card (Loc G 1)^2:= by
   have he:(Fintype.card (Lines G n 1):ℝ)=(n.val:ℝ)^4*Fintype.card (Loc G 1):= by
       have hx:(Fintype.card (Site n):ℝ)=(n.val:ℝ)^4:= by simp [Site,Per,ZMod.card, Four,Axis]
       change ((Fintype.card (Site n × Loc G 1)):ℝ)=_; rw [Fintype.card_prod,Nat.cast_mul,hx]
   unfold skyL; rw [he,mul_pow]
lemma sky_cost (f g:Bid.Dir G n→ℝ)(h:AnalyticAt ℝ f 0)(hp:AnalyticAt ℝ g 0)(hh: ∀ (x y: Site n)(σ τ:TypeFace 1→hue G→ℂ),(∀ k j,‖σ k j‖≤1) → (∀ k j,‖τ k j‖≤1) → |iteratedFDeriv ℝ 2 f 0 ![wave x σ,wave y τ]- iteratedFDeriv ℝ 2 g 0 ![wave x σ, wave y τ]| ≤ w) (v: chain (Lines G n 1) 2):
    |Broc.beam (f∘ arm G n 1) 2 v-Broc.beam (g∘ arm G n 1) 2 v|≤ 1/2*(skyL G n * w):= by
    let A:=Stationary.arm G n 1; let L(F:Bid.Dir G n→ℝ):= iteratedFDeriv ℝ 2 F 0
    let U(k:Fin 2)(x: Lines G n 1):=wave x.1 (torch G n (v k) x)
    have he k: A (dotI (v k))=∑ j:Lines G n 1,U k j:= by rw [into_cell (v k),map_sum]; exact Finset.sum_congr rfl fun i _=> A.apply_symm_apply _
    have hR F(h:AnalyticAt ℝ F 0): Broc.beam (F∘ (arm G n 1)) 2 v=(1/2:ℝ)*∑ x:chain (Lines G n 1) 2,L F (fun i=>U i (x i)):= by
        unfold Broc.beam Tensor.coeff; rw [_root_.smul_apply]; change _ • iteratedFDeriv ℝ 2 (F∘ A.toContinuousLinearMap) 0 _= _; rw [wired A.toContinuousLinearMap (by rw [map_zero];exact h), map_zero, show A.toContinuousLinearMap ∘ (dotI ∘ v)=fun k=>∑ j:Lines G n 1,U k j from funext he,ContinuousMultilinearMap.map_sum (g:=U)]; norm_num; rfl
    rw [hR f h,hR g hp,←mul_sub, abs_mul, abs_of_nonneg (by norm_num : 0≤ (1/2:ℝ))]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← Finset.sum_sub_distrib]; calc
       _ ≤ ∑ x:chain (Lines G n 1) 2, |L f (fun i=>U i (x i))-L g (fun i=> U i (x i))|:= Finset.abs_sum_le_sum_abs ..
       _ ≤ ∑ _:chain (Lines G n 1) 2,w:= by
           refine Finset.sum_le_sum fun i _=>?_ ; rw [show (fun j:Fin 2=> U j (i j))=![U 0 (i 0),U 1 (i 1)] from funext fun j=>by fin_cases j <;> rfl]; exact hh _ _ _ _ (torch_spark (v 0) (i 0)) (torch_spark (v 1) (i 1))
       _ = _:= by simp [chain,skyL]
end YM.FormalBulk08.Hay
