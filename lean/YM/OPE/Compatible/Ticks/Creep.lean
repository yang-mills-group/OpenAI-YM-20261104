import YM.OPE.Compatible.Ticks.Ruler
/-!
# Uniform replenishment. Need only enough logarithmic halos.
Absolute purchase can be different in every lane; compare by ratio, not its own scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Extra.Trajectories
open Function Filter Lattice RG MergeProof Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology Classical
variable {G:Gauge}(C:Family G){i b d j k m:ℕ}
-- rise permitted from finer to now
def Creep (C:Family G)(b d k:ℕ)(v:ℕ→ℝ):Prop:=∀ i,b ≤ i→ i< k→ v i ≤ v (i+1)*(β C (i+1))^d
def gapL (C:Family G)(d i:ℕ):ℕ:= Nat.ceil (64*((d:ℝ)+2)*Real.log (β C (i+1)))
lemma gap_hi(u v:ℝ)(hz:u ≤ v*β C (i+1)^d)(hw:0<v): u ≤ (renal C.path.levels i)*v*Real.exp ((gapL C d i:ℝ)/64):=by
    let x:=β C (i+1); have hx: 0<x:= β_pos ..; have hf: Real.log x≥0:= Real.log_nonneg (β_one C _).le
    have hp: x^(d+2) ≤ Real.exp ((gapL C d i:ℝ)/64):=by
       have hu: 64*((d:ℝ)+2)*Real.log x ≤ gapL C d i:= Nat.le_ceil _; rw [← Real.exp_log hx,← Real.exp_nat_mul]; push_cast; apply Real.exp_monotone; linarith only [hu]
    unfold x at hp; rw [renal_eq]; refine le_trans hz (le_trans ?_ (mul_le_mul_of_nonneg_left hp ?_))
    · rw [pow_add]; change v*x^d ≤ _; rw [show β C (i+1)=x from rfl]; field_simp; norm_num
    change 0≤(x^2)⁻¹*v; positivity
namespace Creep
lemma crop {v:ℕ→ℝ}(h:Creep C k d j v)(ha:k ≤ i)(hb:m ≤ j): Creep C i d m v:= fun _ hx hy=> h _ (ha.trans hx) (hy.trans_le hb)
lemma below {w:ℝ}(hw:0<w): Creep C k d j (Run.Below C.path w j):=by
    intro i _ _; let p:=extent C i; have hP:1 ≤ p:=one_le_two.trans (extent_two ..); let Z i:= Run.Below C.path w j i; have hx(i):0≤Z i:=(Run.below_fee _ hw).le
    refine le_trans (?_ : Z i≤Z (i+1)) (le_mul_of_one_le_right (hx _) (one_le_pow₀ (β_one ..|>.le)))
    unfold Z; rw [Run.below_scale]; exact le_mul_of_one_le_left (hx _) (one_le_pow₀ hP)
lemma purse_stay (w:ℝ)(hp:0<w){k i d:ℕ}(hh:1 ≤ d) : Creep C k d i (purse w (near C.path.levels) k):=by
    have hr(i)(hi:k ≤ i):0 < purse w (near C.path.levels) k i:=by
       induction i,hi using Nat.le_induction with
       | base=> unfold purse; rw [marines _ _ _ (fun _=>hp)]; exact hp
       | succ i hi ih=> unfold purse; rw [march,if_pos hi,near_eq]; exact mul_pos (inv_pos.mpr (β_pos ..)) ih
    intro i hk _; let p:= purse w (near C.path.levels) k; have hp':p i=p (i+1)*β C (i+1):=by
       have he:=β_pos C (i+1); unfold p purse; rw [march,if_pos hk,near_eq]; field_simp
    exact hp'.le.trans (mul_le_mul_of_nonneg_left ((pow_one _).symm.trans_le (pow_le_pow_right₀ (β_one ..|>.le) hh)) (hr _ (hk.trans i.le_succ)|>.le))
variable {C}(A:Allot C)
include A
lemma lamp (hG:G.Simple){w:ℝ}(hw:0<w){k j:ℕ}: Creep C k d j (lantern C.path w d m):=by
    intro i _ _; let p:=lantern C.path w d m; have he:p i=p (i+1)*extent C i^d:=((lan_ratio (i:=i) (d:=d) C.path).symm.trans (mul_comm _ _)) -- risky
    rw [show lantern C.path w d m i=_ from he]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ((block_cheap A _).trans ((β_increases hG).monotone i.le_succ)) _) (lan_pos C.path (i:=i+1) hw|>.le)
omit A
lemma scale (a:ℝ)(hp:0 ≤ a){v:ℕ→ℝ}(h:Creep C k d j v): Creep C k d j (fun i=> a*v i):=by
    intro i hk hi; refine (mul_le_mul_of_nonneg_left (h i hk hi) hp).trans_eq (by ring)
lemma extend {a a' a'':ℕ} {p:ℕ→ℝ} (h:Creep C a k a' p) (hh:Creep C a' k a'' p) : Creep C a k a'' p:= fun i hi hw=> (lt_or_ge i a').elim (fun ht=> h i hi ht) (fun ht=> hh i ht hw)
lemma alter {a:ℕ}{p q:ℕ→ℝ} (h:Creep C a k m p)(hp:∀ i,a ≤ i→ i ≤ m→ q i=p i): Creep C a k m q:=fun i hi hb=> hp i hi hb.le |>.le.trans ((h i hi hb).trans_eq (by rw [hp _ (hi.trans i.le_succ) hb]))
lemma higher {p:ℕ→ℝ}{s:ℕ}(h:Creep C k d j p)(hp:d ≤ s)(hh:∀ i,k < i→ i ≤ j→0≤p i): Creep C k s j p:=fun i hi hn=> (h i hi hn).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (β_one ..|>.le) hp) (hh _ (Nat.lt_succ_of_le hi) hn))
end Creep
end YM.OPE.Allot
