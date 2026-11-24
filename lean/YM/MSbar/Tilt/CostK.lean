import YM.MSbar.Tilt.Poor
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Set
variable {σ:Type}[Fintype σ]
variable {V:Set (Positions σ)} {D K E s B:ℝ}
local notation "ι"=> Positions σ
local notation "L"=> Finset.univ
variable (F:Positions σ→ℝ) {g h:Positions σ} -- remove
noncomputable def moves (x y:Positions σ):ℝ := ∑ i:σ,|y i-x i|
noncomputable def pitch (x y:Positions σ)(s:ℝ) := x+s • (y-x)
lemma route (X Y:Positions σ)(s:ℝ) : HasDerivAt (Tilt.pitch X Y) (Y-X) s:= by have hp:= ((hasDerivAt_id' s).smul_const (Y-X)).const_add X; rw [one_smul] at hp; exact hp
lemma mean (F:ℝ→ℝ)(k:ℝ→ℝ)(h:∀ i:ℝ,i∈Icc (0:ℝ) 1→ HasDerivAt F (k i) i∧ |k i| ≤ B) : |F 1-F 0|≤ B:=by
     have h:= norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=1) (C:=B) (fun i hi=>(h i hi).1.hasDerivWithinAt) (fun i hi=>(h i ⟨hi.1,hi.2.le⟩).2) 1 (right_mem_Icc.mpr zero_le_one); simpa only [sub_zero, Real.norm_eq_abs,mul_one] using h
lemma reports {x:Positions σ} (he:∀ i:σ,|fderiv ℝ F x (bolt i)| ≤ B):|fderiv ℝ F x g|≤ B*moves 0 g:=by
     let K:= fderiv ℝ F x; nth_rw 1 [spiral g]; rw [map_sum]; unfold moves; rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_); rw [map_smul,smul_eq_mul,abs_mul, Pi.zero_apply, sub_zero]; exact (mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)).trans_eq (mul_comm ..)
lemma jointP (X Y:Positions σ)(s:ℝ)(he:Convex ℝ V)(hx:X∈V)(hy:Y∈V)(hs:s∈Set.Icc (0:ℝ) 1): Tilt.pitch X Y s ∈ V:=by
    have hh:=he hx hy (a:=1-s) (sub_nonneg.mpr hs.2) hs.1 (by ring); unfold Tilt.pitch; rw [show _+s •(Y-X)= (1-s) • X+s • Y from ?_];exact hh;rw [smul_sub,sub_smul,one_smul];abel
lemma allV {g h:Positions σ}(I:Set ι)(hv:Convex ℝ I)(hf:∀ x∈I,DifferentiableAt ℝ F x) (he:∀ x∈I,∀ i:σ,|fderiv ℝ F x (bolt i)|≤ B) (hg:g∈I)(hh:h∈I):|F h-F g| ≤B*moves g h:=by
    let a:=Tilt.pitch g h; let f(v:ℝ):=F (a v); have h₁ : f 1= F h:=by unfold f a Tilt.pitch; rw [one_smul,add_sub_cancel]; -- syntax
    have h₂:f 0=F g:=by unfold f a Tilt.pitch;rw [zero_smul,add_zero]
    rw [← h₁,← h₂]; apply mean f (fun v=> fderiv ℝ F (a v) (h-g)); intro i hi; have hx:a i ∈ I:=jointP g h i hv hg hh hi; exact ⟨((hf _ hx).hasFDerivAt.comp_hasDerivAt i (route _ _ _)),by simpa [moves] using (reports (g:=h-g) _ (he _ hx))⟩
lemma stroll (X Y Z W: Positions σ)(hx:‖X-Z‖≤B)(hy:‖Y-W‖≤B)(s:ℝ)(hs:s∈ Set.Icc (0:ℝ) 1) : ‖Tilt.pitch X Y s-Tilt.pitch Z W s‖ ≤ B:=by
    rw [show Tilt.pitch _ _ _-_=Tilt.pitch (X-Z) (Y-W) s from (by unfold Tilt.pitch; simp only [smul_sub]; abel)]; exact (mem_closedBall_zero_iff.mp (jointP (X-Z) (Y-W) s (convex_closedBall 0 B) (mem_closedBall_zero_iff.mpr hx) (mem_closedBall_zero_iff.mpr hy) hs))
lemma slips {V:Set ι}{X Y:Positions σ} (v:σ)(h:∀ y∈V,DifferentiableAt ℝ (fun x:ι=> fderiv ℝ F x (bolt v)) y)(hp:∀ y∈V, ∑ i:σ,|buoy F y [i,v]| ≤ D)(he:Convex ℝ V)(hd:0≤ D)(hX:X∈V)(hY:Y∈V) : |fderiv ℝ F X (bolt v)-fderiv ℝ F Y (bolt v)| ≤ D*‖X-Y‖:=by
     apply Convex.norm_image_sub_le_of_norm_fderiv_le h _ he hY hX
     intro x hx; let A:=fderiv ℝ (fun x:ι=> fderiv ℝ F x (bolt v)) x; apply A.opNorm_le_bound hd; intro t; nth_rw 1 [spiral t]; rw [map_sum,mul_comm D]; refine (norm_sum_le ..).trans ?_; apply le_trans _ (mul_le_mul_of_nonneg_left (hp x hx) (norm_nonneg _)); rw [Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [map_smul,norm_smul]; apply mul_le_mul_of_nonneg_right (norm_le_pi_norm _ _) (norm_nonneg _)
lemma soar {V:Set ι} (f:Positions σ→ℝ) {X X' Y Y':ι}(hv:Convex ℝ V)(hx:X∈V)(hz:X'∈V)(hy:Y∈V)(hZ:Y'∈V)(h₁:‖X'-X‖ ≤ B)(h₂:‖Y'-Y‖ ≤ B)(hk:0 ≤ D)(h:∀ z∈V,ContDiffAt ℝ (↑(2:ℕ)) f z∧ (∀ i:σ, |fderiv ℝ f z (bolt i)| ≤ K) ∧ ∀ i:σ,∑ j:σ,|buoy f z [j,i]| ≤ D):
     |(f Y'-f X')-(f Y-f X)| ≤ K*moves (Y-X) (Y'-X')+D*B*moves X Y:=by
     let v:=Tilt.pitch X Y; let v':=Tilt.pitch X' Y'; let F(t:ℝ):= f (v' t)-f (v t); let P:=fderiv ℝ f; let r:=Y-X; let r':=Y'-X'
     have he : (f Y'-f X')-(f Y-f X)=F 1-F 0:=by unfold F v' v Tilt.pitch; rw [one_smul,one_smul,zero_smul,zero_smul,add_zero,add_zero, add_sub_cancel,add_sub_cancel]; ring
     rw [he]; apply mean F (fun t=>P (v' t) r' -P (v t) r); intro t ht; have hA:v t ∈ V:=jointP X Y t hv hx hy ht; have hA': v' t∈V:=jointP X' Y' t hv hz hZ ht; refine ⟨ ((((h _ hA').1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (Tilt.route ..)).sub (((h _ hA).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (Tilt.route ..))),?_⟩
     let T:= P (v' t)-P (v t); rw [show P _ r' - _ = P (v' t) (r'-r)+ T r from (by unfold T; rw [ContinuousLinearMap.sub_apply, _root_.map_sub _ r' r]; ring)]; refine (abs_add_le ..).trans (add_le_add ?_ ?_)
     · apply (reports f (h _ hA'|>.2.1)).trans_eq; congr 1; simp [moves,r,r']; -- maybe
     nth_rw 1 [spiral r]; rw [map_sum, moves,Finset.mul_sum]; refine (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_); rw [map_smul,smul_eq_mul,abs_mul,mul_comm |r i|]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _) -- inspect?
     apply (slips f i (fun x hx=>((((h _ hx).1.fderiv_right (m:=↑(1:ℕ)) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by simp))) (fun x hx=>(h _ hx|>.2.2 i)) hv hk hA' hA).trans; exact mul_le_mul_of_nonneg_left (stroll _ _ _ _ h₁ h₂ t ht) hk
end YM.MSbar.Tilt
