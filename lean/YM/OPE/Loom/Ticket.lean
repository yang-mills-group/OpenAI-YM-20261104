import YM.OPE.Loom.Shuttle
/-!
# Event/terminal scale costs from the estimates themselves. Charging on both sides of grouping.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker
variable {G:Gauge} {C:Family G} {I J : Type} [Fintype J]{φ : Filter I} {T a c r b : I→ℝ} {m k j : I→ℕ} {A : ℕ→ℝ} {y : ℝ}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "P" => C.path.levels.budget
local notation "δ" => renal C.path.levels
local notation "ψ" => near C.path.levels
local notation "ζ" => fly C.path.levels
set_option quotPrecheck false
variable (hT:Tendsto T φ atTop) (hm:Height C.S φ T m y) (t:ℕ){W r' D}(L : Sharper C W r' D)
include hT hm
lemma renal_coins : Coins φ T (fun i=> δ (m i)) :=by
   refine (Coins.inv (Coins.power (hat_price hT (hm.step (Y).fits.mesh)) hT 2)).congr ?_ (EventuallyEq.refl ..)
   filter_upwards with i; unfold renal Mallow.probe; rw [Real.rpow_neg (show 0≤ X (m i+1) from zero_le_one.trans ((Y).fits.delayed _|>.le)), Real.rpow_two]; rfl
lemma near_coins : Coins φ T (fun i=>ψ (m i)) := Coins.inv (hat_price hT (hm.step (Y).fits.mesh))
lemma fly_coins : Coins φ T (fun i=>ζ t (m i)) := Coins.inv (Coins.power (hat_price hT hm) hT (winter G t))
omit hT hm in
lemma Bi.div (h : Bi φ T a b) (hp:Bi φ T c r)(hx:∀ᶠ i in φ,r i≠0) : Bi φ T (fun i=> a i/c i) (fun i=> b i/r i):= by simpa only [div_eq_mul_inv] using h.mul (hp.inv hx)
lemma price_coin (hh:Bi φ T (C.S.a ∘ j) (C.S.a ∘ m))(h:Bi φ T a b) : Bi φ T (fun i=> priced C (m i) (j i) (a i) (m i)) b:=by
   have hp := hh.div (Bi.refl φ T (C.S.a ∘ m)) (Eventually.of_forall fun _=> (C.S.a_pos _).ne'); have hz:Coins φ T (fun i=> C.S.a (j i)/C.S.a (m i)):= by simpa only [Function.comp_apply,div_self (C.S.a_pos _).ne'] using hp
   unfold priced; simpa only [ite_true, one_mul] using Bi.mul (Coins.mul (renal_coins hT hm) (Coins.power hz hT 4)) h

-- majorant of short group event cost
omit hT hm in
def radiusCost (C : Family G) (l k : ℕ) : ℕ := l*(count C 50 k+10)
include L in
lemma license_polynomial {f:ℕ}(hf:0<f) : Coins φ T (fun i=>license C.path δ f (radiusCost C t (m i)) (m i)):=by
   let q k:=Real.exp ((((P k).supportExponent)+(1:ℝ)/2) * radiusCost C t k)
   have hh: Coins φ T (q ∘ m) := by
     apply Coins.by_le; swap; · filter_upwards with i; simp only [Function.comp_apply,q,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.one_le_exp (mul_nonneg (by rw [L.price]; norm_num) (Nat.cast_nonneg _))
     let e:ℝ:=Real.exp ((110:ℝ)*t*11); have hx:= (Cheap.mul (Bill.const e hT) (Cheap.power (hat_price hT (hm.step (Y).fits.mesh)|>.up) hT (110*t*50)))
     refine hx.norm_le ?_; filter_upwards with i; let k:=m i; let s:= X (k+1); have hh:1<s:= (Y).fits.delayed _
     change ‖Real.exp _‖ ≤ ‖e * s^(110*t*50)‖; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; apply le_trans _ (Real.le_norm_self _); unfold e;
     rw [show s^(110*t*50)=Real.exp (Real.log s*((110*t*50:ℕ):ℝ)) from (by
       rw [mul_comm (Real.log s),Real.exp_nat_mul,Real.exp_log (by positivity)]),←Real.exp_add]; apply Real.exp_monotone
     rw [L.price]; simp only [radiusCost,Nat.cast_mul,Nat.cast_add]; push_cast; let n:ℝ:= count C 50 k; have hp := (show n ≤ 50*Real.log s+1 from by simpa only [Nat.cast_ofNat] using (count_le (C:=C) (f:=50) (i:=k))); have ht :(0:ℝ)≤ t:= Nat.cast_nonneg _
     nlinarith only [ht,mul_le_mul_of_nonneg_left hp ht, mul_nonneg ht (Real.log_nonneg hh.le)]
   exact Coins.div (Coins.mul (Coins.div (renal_coins hT hm) (Bi.const _ (by exact_mod_cast hf.ne') hT)) (renal_coins hT hm)) hh
lemma complete (s: I→ J→ ℝ) (d:J→ I→ℝ) (h:∀ l, Bi φ T (fun i=>s i l) (d l)) (hh:Bi φ T (C.S.a ∘ j) (C.S.a ∘ m)) (n:ℕ) (hn:0<n)(L:Sharper C W r' D) : Bi φ T
    (fun i=> cashIn C.path δ n (radiusCost C t (m i)) (m i) (fun p:J=> priced C (m i) (j i) (s i p) (m i))) (fun i=> ∏ p, d p i):=by
   unfold cashIn; apply Bi.prod hT; intro i _; simpa only [one_mul] using (Bi.mul (license_polynomial (L:=L) hT hm t hn) (price_coin hT hm hh (h i)))
end YM.OPE.Loom
