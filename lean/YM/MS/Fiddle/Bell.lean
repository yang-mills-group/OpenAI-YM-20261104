import YM.MS.Osc.Mesh
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
/-!
# Folding, a smooth branch of the zone. width less 3π/2 and exact integer weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {p q b:ℝ} {i:Cover} {v:QP}
abbrev tier : ℝ:= 2*π
abbrev wide : ℝ:=3*π/2
abbrev inner : ℝ:=π/2
lemma rising : 0<tier:= mul_pos (by norm_num) Real.pi_pos
lemma costing : 0< inner := by unfold inner; positivity
lemma risingW : 0<wide:= by unfold wide; positivity
-- step sin't even, average mirrored.DEF
private def switch (x:ℝ):= Real.smoothTransition (x/π+1/2)
def X0 (p:ℝ):= (switch p+(1-switch (-p)))/2
def bell (x:ℝ):= X0 (x+π)- X0 (x-π)
lemma reflects (p:ℝ): X0 (-p)=1-X0 p:= by rw [X0,X0, neg_neg]; ring
lemma lobeC : Monotone switch:= smoothTransition.monotone.comp (show Monotone (fun x:ℝ=> x/π+1/2) by intro x y h; dsimp only; gcongr)
lemma switch_small {x:ℝ} (h:x≤ -inner): switch x=0:= by refine Real.smoothTransition.zero_of_nonpos ?_; rw [← le_sub_iff_add_le]; apply (div_le_iff₀ Real.pi_pos).mpr; unfold inner at h; linarith
lemma switch_large {x:ℝ} (h:inner≤x): switch x=1:= by refine smoothTransition.one_of_one_le ?_; rw [← sub_le_iff_le_add]; apply (le_div_iff₀ Real.pi_pos).mpr; unfold inner at h; linarith
lemma locus (h:p≤ -inner): X0 p=0:= by unfold X0; rw [switch_small h,switch_large (by linarith)]; ring
lemma upper (h:inner≤p): X0 p=1:= by nth_rw 1 [← neg_neg p]; rw [ reflects,locus (by linarith)]; ring
lemma lobo : Monotone X0:= by intro x y he; unfold X0; gcongr <;> apply lobeC <;> linarith
lemma bell_s (p:ℝ): bell (-p)=bell p:= by unfold bell; rw [show -p+π= -(p-π) by ring,show -p-π= -(p+π) by ring, reflects,reflects]; ring
lemma bell_low (h:p≤ -wide): bell p=0:= by unfold bell; rw [ locus (by unfold wide inner at *; linarith), locus (by unfold wide inner at *; linarith [Real.pi_pos]),sub_zero]
lemma bell_high (h:wide≤p): bell p=0:= by rw [← bell_s, bell_low (by linarith)]
lemma bell_off (h:wide≤ |p|): bell p=0:= (le_abs.mp h).elim bell_high ( fun hx=> bell_low ( by linarith ) ) -- `le_abs` name
lemma bell_1 (h:|p|≤ inner): bell p=1:= by obtain ⟨hu,hv⟩:= abs_le.mp h; unfold bell; rw [upper (by unfold inner at *; linarith),locus (by unfold inner at *; linarith),sub_zero]
lemma bill (p:ℝ): 0≤ bell p := sub_nonneg.mpr (lobo (by linarith [Real.pi_pos]))
lemma toggled (x:ℝ)(h:0≤x)(he:x<tier): bell x+bell (x-tier)=1:= by unfold bell tier at *; rw [upper (by unfold inner; linarith [Real.pi_pos]),show x-2*π+π=x-π by ring,locus (p:=x-2*π-π) (by unfold inner; linarith [Real.pi_pos])]; ring
lemma bell_le (x:ℝ): bell x≤1:= by rcases le_total 0 x with h|h; exact case1 x h; rw [← bell_s]; exact case1 _ (by linarith)
where case1 (p:ℝ)(hp:0≤p): bell p ≤1:= by
                                      by_cases ht:p<tier; · linarith [ toggled p hp ht,bill (p-tier)]
                                      rw [bell_high (by unfold wide tier at *; linarith [Real.pi_pos])]; exact zero_le_one
lemma bell_sm : ContDiff ℝ ∞ bell:= by unfold bell X0 switch; fun_prop
-- fundamental snap.
abbrev deck : Set QP:= Box tier 0
def aisle (x:QP): ℝ:= ∏ i:Axis,bell (x i)
def keepOtp : Finset ℤ:= {0,-1}
def Shells : Finset Cover:= Fintype.piFinset fun _:Axis=> keepOtp
lemma realm (h:v∈deck) (i:Axis): 0≤v i ∧ v i< tier:= by rw [deck,shellsB rising] at h; exact h i (Set.mem_univ i)
lemma scene (p:QP): 0≤ aisle p ∧ aisle p ≤1:= ⟨ Finset.prod_nonneg (fun _ _=> bill ..), Finset.prod_le_one (fun _ _=> bill ..) (fun _ _=> bell_le _) ⟩ -- conflict `bill`
lemma aisle_S (x:QP) : aisle (-x)=aisle x:= by unfold aisle; simp only [Pi.neg_apply,bell_s]
lemma door_n (hp:aisle v ≠ 0): ‖v‖≤ wide:= by apply (pi_norm_le_iff_of_nonneg risingW.le).mpr; intro i; by_contra he; refine hp ?_; exact Finset.prod_eq_zero (mem_univ i) (bell_off (p:=v i) ( le_of_lt (lt_of_not_ge he) )) -- norm Real
lemma door_c (hp:‖v‖≤ inner): aisle v=1:= Finset.prod_eq_one fun i _=> bell_1 (le_trans (norm_le_pi_norm v i) hp)
lemma door_sm : ContDiff ℝ ∞ aisle:= by unfold aisle; apply contDiff_prod; intro i _; exact bell_sm.comp (contDiff_apply ..) -- statement
lemma door_p : HasCompactSupport aisle:= by
   letI : ProperSpace QP:= FiniteDimensional.proper ℝ QP; exact HasCompactSupport.intro (isCompact_closedBall (0:QP) wide) (fun i hi=> by contrapose! hi; exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using door_n hi)) -- lemma name
lemma door_off (hp:i∉Shells)(hv:v∈deck): aisle (v+whole tier i)=0:= by
   simp only [Shells,keepOtp,Fintype.mem_piFinset,Finset.mem_insert, Finset.mem_singleton,not_forall,not_or] at hp; obtain ⟨k,h,h'⟩:=hp; apply Finset.prod_eq_zero (Finset.mem_univ k);
   rw [Pi.add_apply,at_whole]; obtain ⟨hV,hL⟩:= realm hv k; obtain ht|ht:= (show i k>0 ∨ i k<(-1:ℤ) from by omega);
   · have he:1≤(i k:ℝ):= by exact_mod_cast ht
     apply bell_high; unfold tier wide; nlinarith [Real.pi_pos]
   have he : (i k:ℝ)≤ -2:= by exact_mod_cast (show i k≤ -2 from by omega )
   refine bell_low ?_; unfold tier wide at *; nlinarith [ Real.pi_pos ]
lemma merit (hv:v∈deck) : ∑ i∈Shells, aisle (v+whole tier i)=1:= by
    unfold Shells aisle; simp_rw [Pi.add_apply, at_whole]; rw [Finset.sum_prod_piFinset (κ:=ℤ) keepOtp (fun i:Axis=> fun x:ℤ=> bell (v i+tier*x))]; refine Finset.prod_eq_one fun i _=>?_ ; obtain ⟨hh,ht⟩:= realm hv i; simpa [ keepOtp,sub_eq_add_neg] using toggled (v i) hh ht
lemma allT (v:QP): ∃ i:Cover,v+whole tier i∈deck:= by refine ⟨-back tier v,?_⟩; change back tier _=0; rw [add_comm,bo rising,neg_add_cancel]
end YM.MS.Fiddle
