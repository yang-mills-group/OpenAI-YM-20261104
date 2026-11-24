import YM.Contacts.Allium.Rush
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo
/-! # formal deck order medicines. t' old own-g warp, predicted β offset.
 No identity between this and true β presumed. Compute inverse sqrt warp to preserve curvature.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium
open Function Filter Finset Lattice Wilson RG PowerSeries
open Milling Loom
open Resetter Meter
open scoped Topology BigOperators Classical
variable {N:Meter} {k l i:ℕ} {U V:ℕ→Resetter.Pow}{v p:ℝ}
namespace Flux
variable {f g h a b t:Stream}
-- needs eventual grants through k inclusive params clock.
lemma Xbound (ht:N.Rush (-(1/2)) t)(hk:0<k): Looks N t k (fun _=>X) t:= by
   by_cases h:1<k; exact XBound h
   have h:k=1:=(by omega); subst k; refine ⟨fun i _=> Rush.settle (pin (X:Resetter.Pow) i),?_⟩
   rw [show logit t 1 (fun _=>X)=0 from (by ext; simp [logit,pin,coeff_X]),sub_zero]; simpa only [grade,Nat.cast_one,mul_one] using ht
lemma Live.revise (hv:Live U N k)(hV:∀ᶠ i in atTop,V i=U i): Live V N k:= fun j hj=> (hv j hj).take (hV.mono fun _ h=> congrArg (fun x:Resetter.Pow=>pin x j) h)
-- ring morph with eventual tidy
lemma handshake (h:Looks N t k U a)(hb:Looks N t k V b)(hV:∀ᶠ i in atTop,V i=U i): N.Rush (grade k) (a-b):= (sub h.price hb.price).take (hV.mono fun i hi=> by simp only [Pi.sub_apply,logit,hi]; abel)
lemma paste (ht:N.Rush (-(1/2)) t)(hk:2≤k)(hv:Live U N k)(h:∀ᶠ n in atTop,Uniform (U n)): ∀ᶠ i in atTop,1/2<logit t k U i∧logit t k U i<2:= by
   let F:= logit t k U; let B:= logit t 1 U; have hp:= (forecasted ht hv (Nat.one_le_iff_ne_zero.mpr (by omega))).price
   have hB:= N.sliding hp (by unfold grade; norm_num) (1/2) (by norm_num)
   filter_upwards [h,hB] with i hi hv; have hB: logit t 1 U i=1:=(by simp [logit,show pin (U i) 0=1 from hi]); simp only [Pi.sub_apply,hB,Real.norm_eq_abs] at hv; obtain ⟨hh,hg⟩:= abs_lt.mp hv; constructor <;> linarith
lemma invert {g₀:Stream}{d:ℝ}(hd:0<d)(hp:∀ᶠ i in atTop,d≤g₀ i): N.Rush 0 (g₀⁻¹):= (Rush.settle (M:=N) d⁻¹).view (hp.mono fun i hi=> by rw [Pi.inv_apply,Real.norm_of_nonneg (inv_nonneg.mpr (hd.le.trans hi)), Real.norm_of_nonneg (inv_pos.mpr hd).le]; exact inv_anti₀ hd hi)
-- Using β* curvature with polynomial λ, compare with forecast β*S, same Ξ chir through n>2.
variable (ht:N.Rush (-(1/2)) t)(hv:Live U N k)(hk:2≤k)(hu:∀ᶠ i in atTop, Uniform (U i))
def loom (n:ℕ) (A:Resetter.Pow) (x:ℝ) := ∑ j∈ Finset.range n, pin (rotate A) j*x^j
abbrev groom (t:Stream)(k:ℕ)(U:ℕ→ Resetter.Pow) : Stream:= fun i=> loom k (U i) (t i)
local notation "W" => (fun i=> rotate (U i))
local notation "R" => groom t k U
local notation "R'" => (fun i=> (R i)⁻¹^ (2:ℕ))
include ht hv hk
lemma hull : ∀ᶠ i in atTop, 1/2 < R i ∧ R i<2:= paste ht hk (live_turn hv) (Eventually.of_forall fun i=> rotate_zero _)
lemma groom_core:N.Rush 0 R ∧ N.Rush 0 R':= by
   exact ⟨forecast ht (live_turn hv),(invert (show 0<(1/2:ℝ) by norm_num) ((hull ht hv hk).mono fun i hi=>hi.1.le)).powers 2 |>.mono (by norm_num)⟩
include hu
lemma reflect (h:0 < i)(hi:i≤k): Looks N t i U R' := by
   let W':=R; let V:=logit t i U; let H:= fun n=> rotate (U n); have hU:=hu.mono fun i hi=> rotate_share hi; have hV: Live U N i:= fun j hj=>hv j (lt_of_lt_of_le hj hi)
   have h':= (motto (t:=t) hV).multiply ht ((forecasted ht (live_turn hv) hi).powers ht h 2); have hp:= handshake (identity (t:=t) (N:=N) h) h' hU
   refine ⟨hV,(hp.times (groom_core ht hv hk).2 (add_zero (grade i))).take ?_ ⟩
   filter_upwards [hull ht hv hk] with x hx; change (R x)⁻¹^ (2:ℕ)-V x=(1-V x* _)*(R x)⁻¹^ (2:ℕ); rw [Pi.pow_apply]; change _= (1-V x* (R x)^2)* _; have hx:0 < R x:= (by linarith only [hx.1]); field_simp
lemma warp (h:0<l)(hi:l≤k)(j:ℕ): Looks N t l (U*((fun _=>X)* W)^j) (R'*(t* R)^j):=(reflect ht hv hk hu h hi).multiply ht (((Xbound ht h).multiply ht (forecasted ht (live_turn hv) hi)).powers ht h j)
end Flux
open Flux
open PhysicalNext.Repeat Next.Scheduling Clock ConnectedActivityE6 Pressure ConnectedActivityE6.Coat
variable {t b B:Stream}{G:Gauge}
-- real calculator.Delta support.
def shiftβ (b:ℝ)(k:ℕ)(u:Resetter.Pow): ℝ:= b*(loom k u (gStep b))⁻¹^(2:ℕ)
def appeal (b:Stream)(k:ℕ)(U:ℕ→Resetter.Pow):Stream:= fun i=> shiftβ (b i) k (U i)
local notation "K" => appeal b k U
local notation "Y" => gStep ∘ b
local notation "R" => Flux.groom (gStep ∘ b) k U
local notation "ζ" => (fun i=> K i - b i)
abbrev Foil (b:Stream)(N:Meter):Prop:=∀ᶠ i in atTop, inBand (N.β i) (b i)
namespace Foil
variable (hb:Foil b N)
include hb
lemma funded : ∀ᶠ i in atTop,0< b i∧0<Y i∧(Y i)^2*b i=1:= by
   filter_upwards [hb,N.eventual] with i hi hv; have he:0<b i:= (show 0<N.β i/4 by positivity).trans_le hi.1; exact ⟨he,Fare.gS _ he⟩
lemma fare : N.Rush 1 b∧N.Rush (-(1/2)) (Y):= by
   refine ⟨((Rush.any (M:=N) (p:=1)).multiplier 4).view ?_, ((Rush.any (M:=N) (p:=-(1/2))).multiplier 2).view ?_⟩
   · filter_upwards [hb,N.eventual] with i hi hv; refine (Real.norm_of_nonneg (by have h:=hi; obtain ⟨he,hh⟩:=h; linarith)).trans_le (hi.2.trans ((le_abs_self _).trans_eq ?_)); unfold Meter.pow; rw [Real.rpow_one]; rfl -- explicit beta
   filter_upwards [hb,N.eventual,funded hb] with i hi hv hh; rw [Real.norm_of_nonneg hh.2.1.le,Meter.pow,Real.rpow_neg hv.le, ← Real.sqrt_eq_rpow]; apply (band_gap _ _ hv hi).2.trans (le_abs_self _)
-- predicts sign to price record.V.Activity
variable (hk:3≤k)(hv:Live U N k)(hq:∀ᶠ i in atTop,Resetter.Uniform (U i) ∧ QuietPower (U i))
include hk hv hq
-- compares against wallBound.U.average.
lemma trans : ∀ᶠ i in atTop, let r:=R i; r>1/2∧r<2∧0<K i∧ gStep (K i)=r*Y i := by
   filter_upwards [hull hb.fare.2 hv (by omega),hb.funded] with i hi hv r; have hB:= hv.1; have hr:0<r:= (by linarith only [show 1/2<r from hi.1]); have hs:0<K i:= by unfold appeal shiftβ; change 0<b i*r⁻¹^(2:ℕ); positivity
   refine ⟨hi.1,hi.2,hs,?_⟩
   unfold gStep appeal shiftβ; change (Real.sqrt (b i*r⁻¹ ^2))⁻¹=r*(Real.sqrt (b i))⁻¹; rw [Real.sqrt_mul hB.le,Real.sqrt_sq (by positivity)]; field_simp
lemma trend : N.Rush 1 (K):= hb.fare.1.times (groom_core hb.fare.2 hv (by omega)).2 (by norm_num)
lemma born : N.Rush (-(1/2)) (gStep∘ (K)):= ((groom_core hb.fare.2 hv (by omega)).1.times hb.fare.2 (zero_add _)).take ((hb.trans hk hv hq).mono fun _ hi=> hi.2.2.2)
lemma taxes (l:ℕ) (he:0<l) (hh:l≤k): N.Rush (1+grade l) ((K)-b*logit Y l U):= by
   have hv:= hb.fare.1.times ((reflect hb.fare.2 hv (by omega) (hq.mono (fun _ hx=> hx.1)) he hh).price) (show 1+grade l=1+grade l from rfl); refine hv.take ?_; filter_upwards with x; change b x * (R x)⁻¹^(2:ℕ)-b x*_=b x*((R x)⁻¹^(2:ℕ)-_); ring
lemma dimes : N.Rush (-(1/2):ℝ) (fun i=>ζ i-pin (U i) 2):= by
   have hp:= hb.taxes hk hv hq 3 (by norm_num) hk; have hy:1+grade 3= -(1/2:ℝ):=(by norm_num [Flux.grade]); apply ((hy ▸ hp):N.Rush (-(1/2)) ((K)-b*logit Y 3 U)).take; filter_upwards [hq,hb.funded] with i hi hi'; change _-_= K i-b i* logit Y 3 U i; have he:= hi'.2.2; unfold logit; simp only [sum_range_succ,sum_range_zero, show pin (U i) 0=1 from hi.1, zero_add, pow_zero, mul_one, show pin (U i) 1=0 from hi.2 1 (by decide), zero_mul,add_zero]; linear_combination (pin (U i) 2)* he

end Foil
end YM.Contacts.Allium
