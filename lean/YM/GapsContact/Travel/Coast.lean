import YM.GapsContact.Dusk.Shift
import YM.MergeProof.South.Block
import YM.MergeProof.Inns
import YM.MergeProof.North.Bonus
import YM.OPE.Prices.Stock

/-!
# Priced coast to the real dense cell J

Occupancy: site seams aligned, coasting even without spacing. Uses Mug from
Bernoulli `m = basin ...` (cost arithmetic later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Function Finset Filter Lattice RG Push Extra.Histories Source Marker MeasureTheory
open Wilson PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Next.Rank Edition
open PhysicalNext.Repeat.Legato.Bandage MergeProof Accent Menu Overlay
open GridApprox Local Cells Extraction Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)
variable (A:RG.History G) (r:ℕ→ℕ) (D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)) (K:Shipper A r D) (hg:G.Simple)
set_option quotPrecheck false
local notation "β"=> A.levels.clock.hatBeta

include hg in
lemma anti_gate {i j:ℕ}(hi:i ≤ j) : A.levels.clock.hatBeta i ≤ A.levels.clock.hatBeta j:=add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono A.S).monotone hi) (Gauge.slopeConstant_pos hg).le) _ -- version arguments left/right
-- coast term at step `i`, cardinal length J→m only ~ log(log β), choice `coupon` monotone.
lemma coupon_nn {x:ℝ}(h:0<x):0 < coupon x:= Real.rpow_pos_of_pos h _
lemma coupon_le {x:ℝ}(h:1<x): coupon x ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos h.le (by norm_num)
lemma brake_nn {x:ℝ}(h:1<x): 0<aBrake x:=inv_pos.mpr (pow_pos (gate_pos h) _)
lemma brake_le {x:ℝ} (h:1 ≤ gate x) : aBrake x ≤ 1:=inv_le_one_of_one_le₀ (one_le_pow₀ h)
include K in
lemma Shipper.time (m:ℕ) : 1 ≤ gate (A.levels.clock.hatBeta m) ∧ precious (A.levels.clock.hatBeta m) ≤ 1:=by obtain ⟨a,h,ht⟩:= K.grants (m+1) 0 m m.lt_succ_self;exact ⟨ht.price,ht.precise.1⟩

def paceFactor (m i:ℕ) := coupon (β m)* aBrake (β m)^(m-i)
lemma pace_pos (m i:ℕ) : 0 < paceFactor A m i:= mul_pos (coupon_nn (zero_lt_one.trans (A.levels.fits.delayed _))) (pow_pos (brake_nn (A.levels.fits.delayed _)) _)
include K
lemma tour_limit (m i:ℕ): paceFactor A m i ≤ coupon (β m) ∧ paceFactor A m i ≤ 1:=by
   have hp:paceFactor A m i ≤ coupon (β m):=mul_le_of_le_one_right (coupon_nn (zero_lt_one.trans (A.levels.fits.delayed _))|>.le) (pow_le_one₀ (brake_nn (A.levels.fits.delayed _)|>.le) (brake_le (K.time A r D m|>.1)))
   exact ⟨hp,hp.trans (coupon_le (A.levels.fits.delayed _))⟩
include hg
lemma pace_hop (i m:ℕ)(hi:i < m) : paceFactor A m i ≤ aBrake (β (i+1)) * paceFactor A m (i+1) ∧ paceFactor A m i ≤ coupon (β (i+1)):=by
   have hβ:0 < β (i+1):= zero_lt_one.trans (A.levels.fits.delayed _)
   constructor
   · unfold paceFactor; rw [show m-i=m-(i+1)+1 by omega,pow_succ',mul_left_comm];
     apply mul_le_mul_of_nonneg_right (inv_anti₀ (pow_pos (gate_pos (A.levels.fits.delayed _)) _) (pow_le_pow_left₀ (gate_pos (A.levels.fits.delayed _)|>.le) (Real.log_le_log hβ (anti_gate A hg hi)) _)) ((pace_pos A m (i+1)).le)
   exact (tour_limit A r D K m i).1.trans (Real.rpow_le_rpow_of_nonpos hβ (anti_gate A hg hi) (by norm_num))
section
variable (N p m i:ℕ) {o:∀ i:ℕ,V→Site (A.S.side i p)} (w:ℝ)
local notation "R"=> A.rep N p
variable (hm:m ≤ N)
    {f:∀ m:ℕ,V → Config G (A.S.side m p)→ℂ} {g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ}
    {x:Config G (A.S.side m p)→Poly B}
    (h:A.Selected)
-- Mug. At m receives full Serve and dense. Moves through ALL coherent financial stops.
include h
set_option maxHeartbeats 800000 in
lemma continue_ (hX: Integrable x (prior G _)) (hw:0<w) (hh:forall s:V,Wakes A i m N p (fun j=>o j s) (fun _=>w) (fun j=> f j s) (fun j=>g j s) D hm)
    (he:Migrating A i p m o)(hp:∀ j,i ≤ j → j ≤ m→Injective (o j)) (hb:∀ j,i ≤ j→ j < m → 1 ≤ r j)
    (hS:Served (R m) (f m) (tapes A p N g m) x (o m) (fun _=>w) (A.levels.budget m).supportExponent 1)
    (hi:i ≤ m) : Served (R i) (f i) (tapes A p N g i) (gust A N p m x i hi) (o i) (fun _=>paceFactor A m i*w) (A.levels.budget i).supportExponent 1:=by
   let z j (_:V):=paceFactor A m j*w; have hq:0 < precious (β m):=precious_pos (A.levels.fits.delayed m)
   have ht(j)(v:V): 0<z j v:=mul_pos (pace_pos A m j) hw
   have hx: paceFactor A m m ≤ precious (β m):=by
      have hℓ:= A.levels.fits.delayed m; unfold paceFactor precious nice; rw [Nat.sub_self,pow_zero,mul_one]; exact (Real.rpow_le_rpow_of_exponent_le hℓ.le (by norm_num [rBase] : -(2:ℝ)≤ rBase)).trans (le_mul_of_one_le_right (Real.rpow_nonneg (zero_lt_one.trans hℓ|>.le) _) (K.time A r D m|>.1))
   have hA(j:ℕ)(ha:i ≤ j)(hN:j < m) := he.mare j ha hN
   have ht':= windowed A r D N p hm o z (fun _ _=>w) f g h K hh (fun j _ _=> ht j) (fun j _ hj _=> by have h0:= pace_hop A r D K hg j m hj; exact ⟨(mul_le_mul_of_nonneg_right h0.1 hw.le).trans_eq (mul_assoc ..), mul_le_mul_of_nonneg_right h0.2 hw.le⟩) (fun j hj h' => by
      refine ⟨fun x=>(Extra.Multi.Occupancy.of_injective (hp _ (hj.trans j.le_succ) h') x).trans (hb j hj h'),fun x=>(Extra.Multi.Occupancy.of_injective (hp _ hj h'.le) x).trans (hb j hj h'),?_⟩; rw [← hA j hj h']; exact funext fun s=> Ratio.embed_parent ..) (hS.prune (t:=0) (fun _=>hw) (ht _) (slighter (fun _=>hw) (ht _) (by intro j; exact le_refl (paceFactor A m m*w)) (pace_pos A m m|>.le) (tour_limit A r D K m m|>.2)) (pace_pos A m m|>.le) (add_zero _|>.le) ((mul_one _).trans_le hx)) hX i le_rfl hi
   refine ht'.prune (t:=0) (ht i) (ht i) (slighter (ht i) (ht i) (w:=1) (fun v=>(one_mul ..).ge) zero_le_one le_rfl) zero_le_one (add_zero _|>.le) ((one_mul _).trans_le (K.time A r D i|>.2))
end
end YM.GapsContact.Dusk
