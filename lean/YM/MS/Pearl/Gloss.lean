import YM.MS.Pearl.SkyLog
/-!
# Polynomial independence via plow self-similarity
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real Polynomial
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W Y F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ}{s:ℝ}
variable {N:ℕ}(X:ℝ→ Mob G)(hL:X ∈ interest N (Mob G))(hP:∀ y,kPrice (X y)) (hv:∀ t y, plow (-(h:ℂ)) t (X (y+t))=X y)
include hL hP hv
lemma one_tick (m:ℕ)(s:ℝ)(he:m<h): Tad (X s) m=0:= by
   let CC(t:ℝ):= Tad (X t) m; let D:ℝ:=-(h:ℝ)+(m:ℝ); have hD:D<0:= by unfold D; exact_mod_cast (by omega: -(h:ℤ)+m<0)
   let A i (t:ℝ):ℂ:= (((plate N i).eval (s+t):ℝ):ℂ)
   have hx(t:ℝ): Tad (X s) m = ∑ i∈ Finset.range N,(amount (D:ℂ) t*A i t) • CC i := by
      nth_rw 1 [← hv t s]; rw [Tad_scale (hP _), tad_chart X hL hP m (s+t), Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [mul_smul, show (D:ℂ)= -(h:ℂ)+(m:ℂ) by simp [D] ]
   funext k l; apply tendsto_nhds_unique (l:=atTop) (f:=fun t:ℝ=> ∑ i∈Finset.range N,(amount (D:ℂ) t*A i t)* CC i k l) _ _
   · refine tendsto_const_nhds.congr (fun i=>?_); rw [hx i,Finset.sum_apply,Finset.sum_apply]; rfl
   convert tendsto_finsetSum (Finset.range N) (fun i _=> (neg_exp (plate N i) s hD).mul_const (CC i k l)) using 1; simp -- function mismatch use rfl
lemma post_time : ∃ F:Mob G, Home F h∧ F= Tad F h ∧∀ t:ℝ,F=X t:= by
    have hm (t:ℝ): X t=Tad (X t) h:= by
       have hd : haze h (X t)=0:= Finset.sum_eq_zero (fun i hi=> one_tick X hL hP hv _ t (Finset.mem_range.mp hi)); obtain he:= eq_wipe X hL hP hv t; rw [Hem.clear,haze_step,hd,zero_add] at he; exact sub_eq_zero.mp he
    refine ⟨ X 0,(by rw [hm 0]; exact Home.tad (hP 0)), hm 0, fun i=> ?_ ⟩; obtain ht:=hv i 0; rw [zero_add] at ht; exact ht.symm.trans ((by have hu : Home (X i) h:= (by rw [hm i]; exact Home.tad (hP _)); exact hu i) : plow (-(h:ℂ)) i (X i)=X i) -- newline
omit hL hP hv
-- Log Ready weights
lemma sm_ty (t i:ℕ)(F:Mob G): Ready (fun y:ℝ=> ley t i y • F):= by
    let c:= gNat t; let a:= Polynomial.C c * Polynomial.X; let B := (a^i)*Polynomial.C (Nat.factorial i:ℝ)⁻¹; refine ?_; convert status B F using 1; ext; simp [B,a,c,ley,Complex.real_smul,div_eq_mul_inv]; ring_nf; simp
lemma grip (n m ℓ:ℕ)(F:ℂ→Mob G): Ready (priceY n m ℓ F):= by convert Ready.sums (Finset.range (n+1)) (fun i _=> sm_ty ℓ i (ruby (paid m F) (n-i))) using 1; ext; simp [priceY,Finset.sum_apply]
end YM.MS.Pearl
