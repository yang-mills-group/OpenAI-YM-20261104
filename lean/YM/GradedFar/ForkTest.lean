import YM.GradedFar.View
import YM.GradedFar.PhysicalBook
import YM.GradedFar.Sold
/-!
# G4 price on actual input unit balls
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] {P:Prescription F.sector.derivatives}

structure Purchase (I J: Type) where
    x : I → E4
    y : J → E4
    center : E4
    logFrom : ℝ -- r≤ outer
    viewer : Viewers F

variable (d:I→ℕ)(e:J→ℕ)
abbrev weightCost {f:Extraction.Order} {S:Table C.book}{F:Final C f S} (s:ℝ)(z:Purchase F I J):=z.logFrom^(∑i,d i)*s^(∑j,e j)
variable {F}
def Ready (M δ t:ℝ)(x: Purchase F I J): Prop :=0<x.logFrom ∧ x.logFrom≤ t ∧ Setting M δ x.x x.y ∧ x.logFrom*M≤ t*δ

def duo (t:ℝ) (x: Purchase F I J) := badge t* badge x.logFrom
lemma safe_weight {M δ:ℝ}{w:ℝ→Purchase F I J→ℝ}(hx:∀ᶠ t:ℝ in 𝓝[>]0,∀ z, Ready M δ t z → 0 ≤ w t z) :
    Safe (𝓝[>]0) (Ready M δ) duo (fun t z=> w t z/weightCost d e t z):=by
  filter_upwards [(eventually_le_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,hx] with t ht hx z hz
  obtain ⟨hp,he,h,hg⟩:=hz; have hh := hp.trans_le he; constructor
  · apply one_le_mul_of_one_le_of_one_le <;> apply le_add_of_nonneg_right <;> apply neg_nonneg.mpr <;>
      apply Real.log_nonpos <;> linarith
  exact div_nonneg (hx z ⟨hp,he,by assumption,hg⟩) (by dsimp [weightCost]; positivity)

lemma weight_up {M δ s:ℝ}{z:Purchase F I J} (hx:Ready M δ s z): 0< weightCost d e s z:=by
  obtain ⟨hr,ht,hx,h⟩:=hx; have hs:=hr.trans_le ht; dsimp [weightCost]; positivity
lemma transfer_credit {M δ:ℝ} {f' : ℝ→Purchase F I J→ℂ} {w:ℝ→Purchase F I J→ℝ}
    {k:ℕ} {b:ℝ} (hb:0≤b)(hx:∀ᶠ t in 𝓝[>]0,∀ z:Purchase F I J, Ready M δ t z →
      weightCost d e t z * ‖f' t z‖ ≤ b*duo t z^k*w t z) :
    Sold (𝓝[>]0) (Ready M δ) duo (fun s z=>w s z/weightCost d e s z) f':= by
  refine ⟨k,b,hb,hx.mono ?_⟩; intro s hs z he; rw [← mul_div_assoc]; exact
    (le_div_iff₀ (weight_up d e he)).mpr (by rw [mul_comm];exact hs z he)

variable (F) {M δ:ℝ} (hG:G.Simple) (bank:LogTrace F P) (hm:0≤M)(hδ:0<δ)
local notation "ΘU" => Viewers F
local notation "I₁" => Labels S d
local notation "J₁" => Labels S e

def traceCharge (t:ℝ) (z:Purchase F I J) : MultilinearMap ℂ (fun i=> S.Field (d i))
    (MultilinearMap ℂ (fun j=> S.Field (e j)) ℂ) := trace F (move z.center z.logFrom z.x) (move z.center t z.y) z.viewer
variable (P) in
def shadowCharge (h:ℕ) (t:ℝ)(z:Purchase F I J) : MultilinearMap ℂ (fun i=> S.Field (d i))
    (MultilinearMap ℂ (fun j=> S.Field (e j)) ℂ) := shadowError F (move z.center z.logFrom z.x) (move z.center t z.y) z.center h z.viewer P

include bank hG hm hδ
lemma phase_offer (u:I₁)(w:J₁) : Sold (𝓝[>]0) (Ready M δ) duo (fun t (z:Purchase F I J)=> t/weightCost d e t z)
    (fun t z=> (traceCharge F d e t z-traceCharge F d e t {z with viewer := none}) u w) := by
  obtain ⟨k,h⟩:= phase_basis F u w hm hδ bank hG
  refine transfer_credit d e (k:=k) (show (0:ℝ) ≤ 2 by norm_num) (h.mono ?_)
  intro t h z hz; have hz:= h z.logFrom z.center z.x z.y hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 z.viewer
  change weightCost d e t z*‖trace F _ _ z.viewer u w - trace F _ _ none u w‖ ≤ _
  rw [trace_apply,trace_apply]; exact hz

lemma shadow_offer (h:ℕ) (u:I₁)(w:J₁) : Sold (𝓝[>]0) (Ready M δ) duo
    (fun t (z:Purchase F I J)=> (t+(z.logFrom/t)^(h+1))/weightCost d e t z) (fun t z=> shadowCharge F P d e h t z u w) := by
  obtain ⟨b,k,hb,H⟩:= approximate_basis F u w hm hδ bank hG h
  refine transfer_credit d e (k:=k) hb (H.mono ?_)
  intro t h z hz
  specialize h z.logFrom z.center z.x z.y hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 z.viewer
  rw [shadowCharge, shadowError_apply]; exact h

theorem G4_phase (L:ℝ)(hL:0≤L): ∃ k:ℕ, ∃ b:ℝ, 0 ≤ b ∧ ∀ᶠ t:ℝ in 𝓝[>]0,
    ∀(r:ℝ)(o:E4)(x:I→E4)(y:J→E4),0<r → r ≤ t → Setting M δ x y → r*M ≤ t*δ →
    ∀ (v:ΘU) (u:I₁)(w:J₁), (∀ i, ‖u i‖ ≤ L) → (∀ i, ‖w i‖ ≤ L) →
    (r^(∑i,d i)*t^(∑j,e j))*‖whole (spectator F v) (move o r x) u (move o t y) w -
        whole S (move o r x) u (move o t y) w‖ ≤ b*(badge t*badge r)^k*t := by
  obtain ⟨k,b,hb,H⟩:= Sold.both (A:=fun t (z:Purchase F I J)=>
      traceCharge F d e t z-traceCharge F d e t {z with viewer := none})
    (safe_weight d e (w:=fun t (_:Purchase F I J)=>t) (by filter_upwards [self_mem_nhdsWithin] with t (ht:0<t) _ _; exact ht.le))
    (phase_offer F d e hG bank hm hδ) L hL
  refine ⟨k,b,hb,H.mono ?_⟩
  intro t ht r o x y hr he hy hg v u w hu hw; set z:Purchase F I J:=⟨x,y,o,r,v⟩
  have hx: Ready M δ t z:=⟨hr,he,hy,hg⟩
  specialize ht z hx u w hu hw; rw [← mul_div_assoc] at ht
  replace ht:=(le_div_iff₀ (weight_up d e hx)).mp ht; rw [mul_comm] at ht
  change weightCost d e t z*‖trace F _ _ z.viewer u w - trace F _ _ none u w‖ ≤ _ at ht
  rw [trace_apply,trace_apply] at ht; exact ht

theorem G4_invoice (h:ℕ)(L:ℝ)(hL:0≤L): ∃ k:ℕ, ∃ b:ℝ, 0 ≤ b ∧ ∀ᶠ t:ℝ in 𝓝[>]0,
    ∀(r:ℝ)(o:E4)(x:I→E4)(y:J→E4),0<r → r ≤ t → Setting M δ x y → r*M ≤ t*δ →
    ∀ (v:ΘU) (u:I₁)(w:J₁), (∀ i, ‖u i‖ ≤ L) → (∀ i, ‖w i‖ ≤ L) →
      (r^(∑i,d i)*t^(∑j,e j))*‖whole (spectator F v) (move o r x) u (move o t y) w -
        upon (spectator F v) h o (move o t y) w (shadowOld P h (move o r x) o u)‖ ≤
      b*(badge t*badge r)^k*(t+(r/t)^(h+1)) := by
  obtain ⟨k,b,hb,H⟩:= Sold.both (A:=fun t (z:Purchase F I J)=> shadowCharge F P d e h t z)
    (safe_weight d e (show ∀ᶠ t:ℝ in 𝓝[>]0,∀ z:Purchase F I J,Ready M δ t z → 0 ≤ t+(z.logFrom/t)^(h+1) from by
      filter_upwards [self_mem_nhdsWithin] with t (ht:0<t) z hz; have hr:=hz.1; positivity))
    (shadow_offer F d e hG bank hm hδ h) L hL
  refine ⟨k,b,hb,H.mono ?_⟩
  intro t ht r o x y hr he hy hg v u w hu hw; set z:Purchase F I J:=⟨x,y,o,r,v⟩
  have hx: Ready M δ t z:=⟨hr,he,hy,hg⟩
  specialize ht z hx u w hu hw; rw [← mul_div_assoc] at ht
  replace ht:=(le_div_iff₀ (weight_up d e hx)).mp ht; rw [mul_comm, shadowCharge,shadowError_apply] at ht; exact ht
end YM.Integration.GradedFar.Fork
