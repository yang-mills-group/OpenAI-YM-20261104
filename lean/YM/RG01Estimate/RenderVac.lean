import YM.RG01Estimate.RenderInputs
/-!
# Read the Taylor prices for any fixed negative prefactors in a coupling-log exponent.

Producer can use `Office.Roll.plus/active/further` & `Layout.*` when meeting the
packet premises on a finite order vacuum or field model. Here exact analytic input
masses, not evaluation-equivalence classes. Use normalized marks with the same
casts. Atlas exponential price uses nothing about real fields outside.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace.Layout
open Function Filter Set Metric MeasureTheory Finset Matrix
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor Office Courtyard Lapis
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {A E F:Type}[MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℝ E]
    [NormedAddCommGroup F][NormedSpace ℝ F]
variable {b C R v p u:ℝ}{n k r:ℕ}
local notation "X" => ℝ×E
variable (h:A→ℝ × E→ ℝ)
-- Real exponential roll includes arbitrary grade one or higher, with explicit smallness. Atlas independent.
lemma vac_small {q : ℝ}{s:Set A}(hk : MeasurableSet s) {Z:Set E} (p:Roll h s Z b C n)
    (hm: ∀ z∈s,∀ y∈Z,h z (0,y)=0)(hv:C*b≤ 1) (hn:1≤n)(ht:∀ x∈ Set.Icc (-1:ℝ) 1,Brush n q 1 Real.exp x) :
    Roll (fun z=>Real.exp ∘ h z) s Z b (clump n C q) n:= by
   apply p.cumulative _ Real.continuous_exp _ hk; intro i hi x hx
   let r:=x.2; have hV:x.1 ∈ ball (0:ℝ) b:= hx.1; have hr : x.2∈Z:= hx.2; have hb : 0<b:= (norm_nonneg x.1).trans_lt (mem_ball_zero_iff.mp hV)
   let f (t:ℝ):= (h i) (t,r); let L:=ContinuousLinearMap.inl ℝ ℝ E; have hL:‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by simp [L])
   have he(x)(hw:x∈ball (0:ℝ) b): Brush n C 1 f x:= by
      have he t: L t+(0,r)=(t,r):=by simp [L]
      let q:=((0:ℝ),r); have he' t:q+ L t=(t,r):= (add_comm q (L t)).trans (he t)
      have hf:= Lantern.skim (P:=L) x ((he' _) ▸ p.occupied i hi (x,r) (show _ from ⟨hw,hr⟩)) hL; simp only [he'] at hf; exact hf
   have hf:= (convex_ball (0:ℝ) b).norm_image_sub_le_of_norm_fderiv_le (fun i hi=>(((he i hi).smaller hn).smooth).differentiableAt (by norm_num))
       (fun i hi=> by rw [←norm_iteratedFDeriv_one]; exact (Brush.offer.mp (he i hi)).inside 1 hn) (mem_ball_self hb) hV
   rw [show f 0=0 from hm i hi x.2 hr,sub_zero,sub_zero] at hf
   exact ht _ (abs_le.mp (hf.trans ((mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx.1).le (p.occupied i hi x hx).nonneg).trans hv))) -- defeq
lemma vac_atlas [NormedAddCommGroup A][BorelSpace A] {s:Set E} (p:Atlas h s k n C)
    (hm : ∀ z, ∀ y∈ s,h z (0,y)=0)(hn:1≤n)(hC:0≤ C)(hv : 0≤v)(ht:∀ x∈ Set.Icc (-1:ℝ) 1,Brush n v 1 Real.exp x) :
    Atlas (fun z=> Real.exp ∘ h z) s (k*n+0) n (clump n C v):= by
   constructor; intro q hq
   obtain ⟨a,ha,H⟩:=p.supply q hq; let b:=1+q; have hb:0≤b:=add_nonneg zero_le_one hq.le
   let c:= C*b^k; have hc:0≤c:=mul_nonneg hC (pow_nonneg hb _); let d:=min a (1+c)⁻¹
   have he:0< 1+c:=add_pos_of_pos_of_nonneg zero_lt_one hc; have hT:0<d:=lt_min ha (inv_pos.mpr he)
   have hh:= vac_small h (measurableSet_closedBall) (H.of_le le_rfl (min_le_left a ((1+c)⁻¹)) le_rfl) (fun z _ y hy=>hm z y hy)
      (show c*d≤ 1 from (mul_le_mul (le_add_of_nonneg_left zero_le_one) (min_le_right ..) hT.le he.le).trans_eq (mul_inv_cancel₀ he.ne')) hn ht
   exact ⟨d,hT, hh.of_le (clump_price (n:=n) (show 1≤b from le_add_of_nonneg_right hq.le) (le_refl (C*b^k)) hc (show v ≤ v*b^0 by simp) hv) le_rfl le_rfl⟩

-- e permits raw positive power too: charge as resolved pages of a valuation
-- through a finite power (apply also after multiplying by b^e using Roll.active).
def wear (f : A → ℝ × E→ F)(r : ℕ) (z:A) : X→ F:= pages (f z) r
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma delivered {S:Set A}{Z:Set E} {g:A → ℝ × E→ F}(p:Roll g S Z b C (n+r)) (hp:IsOpen Z) (h:∀ i∈S,∀ y∈Z,∀ k<r,piece (g i) k y=0) :
    ∀ i∈S, ∀ x∈ corridor b Z, g i x=x.1^r • wear g r i x := fun i hi x hx=> priced_pole (g i) Z b hp r (h i hi) (p.occupied i hi) x hx
end YM.RG01Estimate.Laplace.Layout
