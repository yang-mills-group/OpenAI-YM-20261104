import YM.GradedFar.PriceStep
/-!
# One-step Z price (two directions). Retain first-order smallness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Finset Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Fleet MS.Tide FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open Fork (Coat)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (F:Final C fo S)(J:ℝ→tower S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {h:ℕ}
local notation "g" => strength G
local notation "Role" => Fork.Cast F R h
local notation "Φ" => Fork.Cast.cost F R
lemma conservative_aux {ι:Type}[Fintype ι]{x y w:ℂ}{D b k:ℝ} (f h:ι→ℂ) (hk:‖x*y*w‖ ≤ b) (hq:‖x‖≤k)
    (hf:∀ i,‖f i‖≤D)(hb:∀ i,‖h i‖≤b)(hD:0≤D):
    ‖x*(y*w + ∑ i,f i*h i)‖ ≤ (1+k*Fintype.card ι*D)*b:=by
  rw [_root_.mul_add, ← mul_assoc]; apply (norm_add_le ..).trans
  have hc : ‖∑ i,f i*h i‖ ≤ (Fintype.card ι:ℝ)*(D*b):=
    (norm_sum_le ..).trans (le_trans (b:=∑ _ : ι,D*b) (Finset.sum_le_sum fun i _=> by
        rw [norm_mul]; exact
          mul_le_mul (hf i) (hb i) (norm_nonneg _) hD) (by simp))
  rw [norm_mul x (∑ i,f i*h i)]
  exact (add_le_add hk (mul_le_mul hq hc (norm_nonneg _) ((norm_nonneg x).trans hq))).trans_eq (by ring)

private lemma coupon(r:ℝ)(a:ℝ)(H:0 ≤ r)(h:0 < a)(k:ℕ): ‖((r:ℂ)/ (a:ℂ))^k‖=(r/a)^k:=by
  rw [norm_pow,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg H,Real.norm_of_nonneg h.le]
private lemma edge {r s:ℝ}(hp:0<r)(hs:0<s)(hr:s ≤ r) (i j:ℕ)(h:i ≤ j) :(r/s)^i * (s/r)^j ≤ 1:=by
  rw [← inv_div s r,inv_pow,mul_comm] -- inv_div s r orientation
  rw [← div_eq_mul_inv]; apply (div_le_one (pow_pos (div_pos hs hp) _)).mpr; exact
    pow_le_pow_of_le_one (div_nonneg hs.le hp.le) ((div_le_one hp).mpr hr) h

lemma front_cap (p:Role)(i:Toon G h){r s k b:ℝ}(hp:0<r)(hr:r/2 ≤ s)(hs:s≤r)(hb:0≤ b) (hfund:∀ i, ‖front F J R r p i‖ ≤ b)
    (hcut: Φ p < heft (Dframe.flash i) → front F J R r p i=0)(hk:opField (delta J h s r) ≤ k)(hK:0 ≤ k):
    ‖front F J R s p i‖ ≤ (1+2^h * (Fintype.card (Toon G h):ℝ)*k)*b:= by
  have hq:0<s:=(half_pos hp).trans_le hr
  rw [front_rule F J R hp hq]
  apply conservative_aux _ _ ?_ ?_ (fun j=> priced_step J hk j i) hfund hK
  · by_cases H: Φ p < heft (Dframe.flash i); · rw [hcut H,mul_zero,norm_zero]; exact hb
    rw [norm_mul,norm_mul,coupon s r hq.le hp,coupon r s hp.le hq]; exact
      (mul_le_mul ((mul_comm ..).trans_le (edge hp hq hs _ _ (le_of_not_gt H))) (hfund i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [coupon s r hq.le hp]; exact (pow_le_one₀ (by positivity : 0 ≤ s/r) ((div_le_one hp).mpr hs)).trans (one_le_pow₀ (by norm_num))

lemma after_cap (p:Role)(i:Toon G h){r s k b:ℝ}(hp:0<r)(hr:r/2 ≤ s)(hs:s≤r)(hb:0≤ b) (hfund:∀ i, ‖after F J R r p i‖ ≤ b)
    (hcut: heft (Dframe.flash i)<Φ p → after F J R r p i=0)(hk:opField (delta J h r s) ≤ k)(hK:0 ≤ k):
    ‖after F J R s p i‖ ≤ (1+2^h * (Fintype.card (Toon G h):ℝ)*k)*b:= by
  have hq:0<s:=(half_pos hp).trans_le hr; rw [after_rule F J R hp hq]
  apply conservative_aux _ _ ?_ ?_ (fun j=> priced_step J hk i j) hfund hK
  · by_cases H: heft (Dframe.flash i) < Φ p; · rw [hcut H,mul_zero,norm_zero]; exact hb
    rw [norm_mul,norm_mul,coupon r s hp.le hq,coupon s r hq.le hp]; exact
      (mul_le_mul (edge hp hq hs _ _ (le_of_not_gt H)) (hfund i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [coupon r s hp.le hq]; exact (pow_le_pow_left₀ (show 0 ≤ r/s by positivity) (halves hp hr hs).2.2 _).trans
     (pow_le_pow_right₀ (by norm_num) (Fork.Cast.costs F R p))

def Exposure (h:ℕ)(r b:ℝ): Prop:= ∀ (i: Fork.Cast F R h) (u:Toon G h), ‖front F J R r i u‖ ≤ b ∧ ‖after F J R r i u‖ ≤ b

variable (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
    (heard:∀ i (hi:i≤h), Included F J i h hi) {t:ℝ→ℝ} (stamp:Stamp J Z M ν t h 1)
include heard stamp H
lemma exposes : ∃ C:ℝ,0≤C ∧ ∀ᶠ r:ℝ in trail,∀ s,r/2 ≤ s → s ≤ r → ∀ b,0≤b → Exposure F J R h r b →
    Exposure F J R h s ((1+C*g r^2)*b) := by
  obtain ⟨C,hC,hv⟩:= micro J Z M ν H h stamp; have hp:= eventually_all.mpr fun i:Fin (h+1)=>
    heard i.val (Nat.le_of_lt_succ i.isLt); refine ⟨2^h*(Fintype.card (Toon G h):ℝ)*C,by positivity,?_⟩
  filter_upwards [hv,hp,self_mem_nhdsWithin] with r h₁ h₂ (hr:0<r) s ha hs b hb hi x y
  obtain ⟨hd,hk⟩:= h₁ s ha hs
  have ht: 0 ≤ C*g r^2:=by positivity
  rw [mul_assoc (2^h*(Fintype.card (Toon G h):ℝ)) C]; exact ⟨
    front_cap F J R x y hr ha hs hb (fun i=>(hi x i).1) (fun hh=>admit_front F J R x (h₂ x.1) y hh) hk ht,
    after_cap F J R x y hr ha hs hb (fun i=>(hi x i).2) (fun hh=>admit_after F J R y (h₂ y.1) x hh) hd ht⟩
theorem envelope : ∃ C:ℝ,0≤C ∧ ∃ p:ℕ, ∀ᶠ r in trail, Exposure F J R h r (C*OPE.Log.badge r^p):= by
  obtain ⟨C,hc,H⟩:= exposes F J R Z M ν H heard stamp; refine Dyadic.iterate hG _
    (fun {r s b} h g₀ i j=> ⟨(h i j).1.trans g₀,(h i j).2.trans g₀⟩) (fun r _=>?_) hc H
  choose b₁ hb₁ using fun p:Role=> Finite.exists_le (fun i:Toon G h=> max ‖front F J R r p i‖ ‖after F J R r p i‖)
  obtain ⟨b,hb⟩:= Finite.exists_le b₁; refine ⟨max 0 b,le_max_left ..,?_⟩; intro i j; have h:=(hb₁ i j).trans
    ((hb i).trans (le_max_right 0 b)); exact ⟨(le_max_left ..).trans h,(le_max_right ..).trans h⟩
end YM.Integration.GradedFar.Neighbor
