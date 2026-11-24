import YM.OPE.Gallery.Pose
import YM.OPE.Log.Pricing
/-!
# Wider mint to actually recover all sleeper radii on ancestor comparisons
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Filter Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage ManyCopies
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ι I:Type*}{l: Filter ι}{T x:ι→ℝ}{a:ℝ}
    {m k:ι→ℕ}{W r D}(L : LogPackage C W r D)(hG:G.Simple)
local notation "Y"=> C.path.levels
local notation "S'"=> C.path.levels.budget
local notation "Γ"=> C.path.levels.clock
local notation "β"=> C.path.levels.clock.hatBeta
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
variable (hT:Tendsto T l atTop)
include L
lemma meterExists (i:ℕ) : ∃ w,8≤ w ∧ 1 ≤ δ i*η i* mintK w:= ⟨(S' i).B,L.system.costs.stay.support i (Nat.zero_le _), L.system.costs.stay.mint i (Nat.zero_le _)⟩
def meter (i:ℕ) := Nat.find (meterExists L i)
lemma meters (i:ℕ): 8≤ meter L i∧ meter L i ≤ (S' i).B ∧ 1 ≤ δ i*η i*mintK (meter L i):=by have ht:= Nat.find_spec (meterExists L i); exact ⟨ht.1, Nat.find_min' (meterExists L i) ⟨ L.system.costs.stay.support _ (Nat.zero_le _), L.system.costs.stay.mint _ (Nat.zero_le _)⟩, ht.2⟩
omit L
include hG
lemma beta_mono : Monotone (C.path.levels.clock.hatBeta):= fun i j h=> add_le_add_right (mul_le_mul_of_nonneg_left ((scale_mono _).monotone h) (show 0 ≤ G.slopeConstant from (Gauge.slopeConstant_pos hG).le)) _
lemma flyAnti (d:ℕ): Antitone (fly C.path.levels d):= fun i j h=> inv_anti₀ (pow_pos (zero_lt_one.trans ((Y).fits.delayed i)) _) (pow_le_pow_left₀ (zero_le_one.trans ((Y).fits.delayed i).le) (beta_mono hG h) _)
lemma nearAnti : Antitone (near C.path.levels):= fun i j h=> inv_anti₀ (zero_lt_one.trans ((Y).fits.delayed _)) (beta_mono hG (Nat.succ_le_succ h))
omit hG
include L
lemma meter_mono (hG:G.Simple): Monotone (meter L):= fun i j hij=> Nat.find_min' _ ⟨(meters L j).1, (meters L j).2.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul (renalAnti L hG hij) (nearAnti hG hij) (L.system.costs.stay.water _ (Nat.zero_le _)|>.1.le) (L.system.costs.stay.water _ (Nat.zero_le _)|>.2.le)) (Real.exp_pos _).le)⟩
lemma meter_upper (i:ℕ): (meter L i:ℝ) ≤ 512*Real.log (C.path.levels.clock.hatBeta (i+1))+9:=by
    let x:=β (i+1); let u:=512*Real.log x; let y:=Nat.ceil u
    have hv:1<x:=(Y).fits.delayed _; have hx:0<x:=zero_lt_one.trans hv; have hp:0 ≤ u:= mul_nonneg (by norm_num) (Real.log_nonneg hv.le); have hu:u ≤ y:= Nat.le_ceil _; have hy:x^3 ≤ mintK (y+8):= by
        unfold mintK; calc
          x^3=Real.exp ((↑(3:ℕ):ℝ)*Real.log x):= by rw [Real.exp_nat_mul,Real.exp_log hx]
          _ ≤ _:=by apply Real.exp_monotone; push_cast; unfold u at hu; linarith only [hu,Real.log_nonneg hv.le]
    have hf: meter L i ≤ y+8:=Nat.find_min' _ ⟨by omega,by rw [price_paid,show η i=x⁻¹ from rfl,show (β (i+1)^2)⁻¹ *x⁻¹=(x^3)⁻¹ from by rw [pow_succ x 2,mul_inv_rev,mul_comm],mul_comm, ← div_eq_mul_inv]; exact (one_le_div (pow_pos hx 3)).2 hy⟩
    have hg : (meter L i:ℝ) ≤ (y+8:ℕ):= Nat.cast_le.mpr hf; push_cast at hg; change (meter L i:ℝ) ≤ u+9; linarith only [hg, show (y:ℝ)< u+1 from Nat.ceil_lt_add_one hp]

def lamina (H i:ℕ) := license C.path δ H (meter L i+2) i
lemma laminaPos {H:ℕ}(he:0<H)(i:ℕ):0<lamina L H i:= license_pos _ _ (L.system.costs.stay.water _ (Nat.zero_le _)|>.2) he
lemma lamina_le {H:ℕ}(he:0<H)(i:ℕ):lamina L H i ≤ 1:=by
    let x:= (S' i).supportExponent+1/2; have hU:0<δ i:=(L.system.costs.stay.water _ (Nat.zero_le _)).2; have ht:=renal_le L i; let y:=δ i; have hx:1 ≤ (H:ℝ):=(by exact_mod_cast he);
    refine (div_le_self (mul_nonneg (by change 0 ≤ δ i/H; positivity) hU.le) (Real.one_le_exp (mul_nonneg (add_nonneg (S' i).exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)))).trans ((mul_le_of_le_one_left hU.le ((div_le_self hU.le hx).trans ht)).trans ht)
include hG
lemma laminaAnti (H:ℕ)(h:0<H): Antitone (lamina L H):= by intro i j hj; have hR:=renalAnti L hG hj; have hK(k):= (show 0≤δ k from (L.system.costs.stay.water k (Nat.zero_le _)|>.2.le)); have he: meter L i ≤ meter L j:=meter_mono L hG hj; unfold lamina license; simp_rw [show ∀ i,(S' i).supportExponent=(100:ℝ) from L.support]; have ht:=hK j; have hu:=hK i; gcongr
omit hG
include hT
lemma lamina_stamp {H:ℕ} (h:0<H)(hk:Height C.S l T k a): ValueStamp l T (fun i=> lamina L H (k i)):=by
   let p i:=meter L (k i)+2; let f i:= Real.exp ((100+(1/2:ℝ))* p i); let x i:=β (k i+1)
   have hx:ValueStamp l T x:= betaStamp hT (hk.step (Y).fits.mesh)
   have he(i): Real.log (f i) ≤ (100+(1/2:ℝ))*11+ 51456*Real.log (x i):= by
       have hh : (p i:ℝ) ≤ 512*Real.log (x i)+11:=by unfold p; push_cast; linarith only [show (meter L (k i):ℝ) ≤ 512*Real.log (x i)+9 from meter_upper L _]
       unfold f; rw [Real.log_exp]; linarith only [hh]
   have hf: ValueStamp l T f:=by
       refine ⟨Eventually.of_forall fun _=>Real.exp_pos _, ?_,(ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=>one_pos) (Eventually.of_forall fun i=> Real.one_le_exp (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))⟩
       apply ((Wallet.const hT (Real.exp ((100+(1/2:ℝ))*11))).mul (hx.up.pow hT 51456)).of_le' (Eventually.of_forall fun _=> Real.exp_pos _)
       filter_upwards [hx.profit] with i hi; let y:= Real.exp ((100+(1/2:ℝ))*11); have hz:y*x i^51456=Real.exp ((100+(1/2:ℝ))*11+51456*Real.log (x i)):= by rw [Real.exp_add,show (51456:ℝ)= (↑(51456:ℕ):ℝ) from (by norm_num),Real.exp_nat_mul,Real.exp_log hi]
       rw [show Real.exp _*x i^51456= _ from hz]; exact Real.le_exp_of_log_le (he i)
   have hd:=renalStamp hT hk; unfold lamina license; simp_rw [show ∀ i,(S' i).supportExponent=(100:ℝ) from L.support]; exact (((hd.div (ValueStamp.const hT (Nat.cast_pos.mpr h))).mul hd).div hf)
end YM.OPE.Log
