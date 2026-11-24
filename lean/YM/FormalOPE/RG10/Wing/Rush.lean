import YM.FormalOPE.RG10.Wing.Power
/-! # Finite jet clock compatibility for gauge shifts. Never an assumed estimate on
 perturbative $D^n(p)$ transferred older. Needs $kick` nilpot through order for each
 relevant rank.K.Stamped construction supplied later. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing
open Function Finset PowerSeries Route Cycle
open scoped Topology BigOperators Classical
variable {X Y : Type} [Fintype X] (u:X→Channel X)
variable (P:Channel X)
local notation "♥"=> numeral (kick u)
local notation "Δ"=> kick u
variable {k a b c:ℕ}
def tender (a:ℕ) : Channel X→ₗ[ℂ] Channel X:=∑ i∈range a, numeral (kick u) i
lemma touch : tender u a P=∑ i∈range a,♥ i P:= by unfold tender; rw [LinearMap.sum_apply];
lemma coin_move {P Q:Channel Y}(h:Through k P Q)(c:ℂ): Through k (c • P) (c • Q):= by intro i hi; rw [coeff_smul,coeff_smul,h i hi]
lemma clear {P Q:Channel X}(he:Through k P Q): Through k (♥ a P) (♥ a Q):= coin_move (skew_power u he a) _
lemma political {P Q:Channel X}(he:Through k P Q): Through k (tender u a P) (tender u a Q) := by intro i hi; simp_rw [touch,map_sum]; exact sum_congr rfl (fun a _=> clear (a:=a) u he i hi)
-- $N>0$ at which all further iterates vanish through k. Exhaust

def Expiring (u:X→Channel X)(P : Channel X)(k a:ℕ): Prop := 0<a ∧ Through k (numeral (kick u) a P) 0
lemma WardGiven (he: Through k (kick u P) 0): Expiring u P k 1:= by refine ⟨by decide,?_⟩; rw [show 1=0+1 from rfl,thick_stamp]; simpa using he -- precise_zero, inv etc maybe rewrite goal wrong
lemma Expiring.off {u:X→Channel X}{P:Channel X}(h:Expiring u P k a)(ht : a≤b): Expiring u P k b:= by
 induction b,ht using Nat.le_induction with
 | base=>exact h
 | succ b ht ih=> refine ⟨Nat.zero_lt_succ _,?_⟩; rw [thick_stamp]; simpa only [map_zero, smul_zero] using coin_move (skew u ih.2) ((↑b+1:ℂ)⁻¹)
-- binder types? declare {u P} explicit needed
lemma Expiring.later {u:X→Channel X}{P:Channel X}(h:Expiring u P k a)(ht : a ≤ b): Through k (tender u b P) (tender u a P):= by
 intro i hi; simp_rw [touch,map_sum]; symm; apply sum_subset (range_mono ht); intro j _ hj;
 exact ((h.off (by contrapose! hj; simp [hj])).2 i hi).trans (map_zero (coeff i))

lemma Expiring.above (he:∀ i,Guard (u i) k 1)(hg:steadyDown u) (d:ℕ)(ht:Guard P k d): Expiring u P k (cycle d k) := ⟨by unfold cycle; positivity, shutdown u P hg ht he⟩
lemma expires (he:∀ i,Guard (u i) k 1)(hg:steadyDown u): ∃ a, Expiring u P k a:= by
 let d:= (range (k+1)).sup (fun j=>(coeff j P).totalDegree);
 exact ⟨cycle d k, Expiring.above u P he hg d fun j hj=> (Finset.le_sup (f:=fun j=>(coeff j P).totalDegree) (mem_range.mpr (show j<k+1 by omega))).trans (Nat.le_add_right ..)⟩
-- use spread $t≥a+b$
variable {U Q : Channel X} (H : Expiring u U k a)(G:Expiring u Q k b)
include H G in
lemma sandwich (hc:a+b ≤ c) : Through k (tender u c (U*Q)) (tender u a U * tender u b Q):= by
 simp_rw [touch, Cycle.pascal (kick u) U Q]; rw [←sum_biUnion,Finset.sum_mul_sum,←Finset.sum_product']; swap -- inspect
 · intro i _ j _ h; apply disjoint_left.mpr; intro t ht he; exact h ((mem_antidiagonal.mp ht).symm.trans (mem_antidiagonal.mp he))
 intro i hi; rw [map_sum,map_sum]; symm
 apply sum_subset; · intro x hx; have hv:= mem_product.mp hx; refine mem_biUnion.mpr ⟨x.1+x.2,mem_range.mpr (by obtain ⟨ht,hh⟩:=hv; simp only [mem_range] at ht hh; omega),mem_antidiagonal.mpr rfl⟩
 intro x _ hx; by_cases h:x.1<a
 · have he : b≤x.2:= by contrapose! hx; simp [hx,h]
   have hv:= (Through.mul (Through.refl (♥ x.1 U)) (G.off he).2) i hi; simpa only [mul_zero,map_zero] using hv
 have he:= ((H.off (le_of_not_gt h)).2.mul (Through.refl (♥ x.2 Q))) i hi; simpa only [zero_mul,map_zero] using he
-- abstract representation
variable (Q': Channel X)
def Forward (u:X→Channel X)(P Q:Channel X)(k:ℕ): Prop := ∃ a, Expiring u P k a ∧ Through k (tender u a P) Q
namespace Forward
variable {u P Q'}
lemma latest (H : Forward u P Q' k)(he:Expiring u P k a) : Through k (tender u a P) Q':= by
 obtain ⟨m,hm,h⟩:= H; exact ((he.later (le_max_left a m)).symm.trans (hm.later (le_max_right a m))).trans h
lemma congr (h:Forward u U Q k)(hp:Through k U P)(hq:Through k Q Q'): Forward u P Q' k:= by
 obtain ⟨t,ht,h⟩:= h; exact ⟨t, ⟨ht.1,(clear u hp).symm.trans ht.2⟩, ((political u hp).symm.trans h).trans hq⟩
variable (he : ∀ i,Guard (u i) k 1) (hg:steadyDown u) (h₁:Forward u U Q k)(h₂: Forward u P Q' k)
include he hg h₁ h₂
lemma add : Forward u (U+P) (Q+Q') k:= by
 obtain ⟨n,hn⟩:=expires u (U+P) he hg; obtain ⟨a,ha⟩:= expires u U he hg; obtain ⟨b,hb⟩:= expires u P he hg; let x:= a+b+n
 refine ⟨x,hn.off (by unfold x; omega),?_⟩; rw [map_add]; exact Through.add (latest h₁ (ha.off (by unfold x; omega))) (latest h₂ (hb.off (by unfold x;omega)))
lemma mul : Forward u (U*P) (Q*Q') k:= by
 obtain ⟨n,hn⟩:=expires u (U*P) he hg; obtain ⟨a,ha⟩:= expires u U he hg; obtain ⟨b,hb⟩:= expires u P he hg; let x:= a+b+n
 exact ⟨x,hn.off (by unfold x; omega), (sandwich u ha hb (c:=x) (by unfold x; omega)).trans (Through.mul (latest h₁ ha) (latest h₂ hb))⟩
omit he hg h₁ h₂
lemma ofWard (H : Through k (kick u U) 0): Forward u U U k := by refine ⟨1,WardGiven u U H,?_⟩; rw [touch]; simpa using Through.refl U
end Forward
end YM.FormalOPE.RG10.Wing
