import YM.RG16.GaugeCredit.Ages

/-!
# Keep the soft terminal error out of the readout

Engineer first in k mesh units (translator `ScaleIn` price already in local
hypotheses). Use exact report at each step, including wrapping drift via the
intrinsic periodic fit. This identity makes every jump in the returned
normalized reports a comparison of **stable residuals**, excluding the
possibly now-rare volume charge. Bound the tail BEYOND the short window by
the **real** capture budget and its true measured projection. No analytic
model charged at this tail. So don't need analytic models r-accurate all the
way to the long stop: reserve that age for the coefficient cut only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Function Filter Set Lattice Wilson RG Source MeasureTheory
open Extra.Histories Relay Bid Cells Push.Local Pert Trace.Physical Trace.Physical.GermGraph
open Literal Work.G08 MergeProof OPE Next.Foundations Push.GridApprox
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(C:Family G)(H:C.Makes)(N p d k:ℕ)
set_option quotPrecheck false
local notation "Λ" => Lambda C.path.levels
local notation "μ" => coin C
local notation "P" => C.path.levels
local notation "V" => C.label d
local notation "X" => measuring C d N p
local notation "w" => C.labels.level d
local notation "s" => (w).coeffSize
local notation "t" => factor C
local notation "τ" => transition (C:=C) d N p
local notation "W" => calValues (C:=C) d N p
local notation "Y'" => mCost C d N p

structure Region (u b:ℕ)(γ:ℝ) : Prop where
   openGate (i:ℕ) : u≤ i→ i≤b→ Opened C d i p
   cross (i:ℕ) : u≤ i→ i<b → Gate C d N p i γ 1
   cut (i:ℕ) : u ≤ i→ i<b → factor C i^(-rate)*factor C i^γ ≤ 1/2
lemma cal_shift {i:ℕ}(c:ℂ)(f:Config G (C.side (i+1) p) → ℂ)(hf:Integrable f (prior G (C.side (i+1) p))) : τ i (c • f) = c • τ i f := by
   unfold transition blast; rw [StepData.push_smul _ _ _ _ hf,smul_comm]

variable (f:Cut C N p)
open scoped Classical in
def precredit (i:ℕ) := if hi:i ≤ N then (alto C.path k d) • credit C N p d f i hi else 0
open scoped Classical in
def Prequote (i:ℕ) := if m:Opened C d i p then if hi:i≤N then alto C.path k d • topReport C N p d H i m hi f else 0 else 0
open scoped Classical in
def funded (i:ℕ) (x:C.label d):= if hi:i ≤ N then if hp:Opened C d i p then (fitting d N p i H hp hi).symm x else 0 else 0
variable {k} {u b i l j : ℕ} {D r γ:ℝ}{y z x:C.label d} -- k implicit or not?
local notation "B" => precredit C N p d k f
local notation "R" => Prequote C H N p d k f
local notation "map₀" => funded C H N p d
local notation "μ₀" => (fun i:ℕ=> (t i)^(-rate))

lemma fund_as (hN:i ≤ N)(hp : Opened C d i p)(x:C.label d) : X i (map₀ i x)=x := by
   unfold funded; rw [dif_pos hN, dif_pos hp]; exact (fitting d N p i H hp hN).apply_symm_apply _
include H
omit H in
lemma pre_step (hf:Continuous f)(hi:i<N): B i= τ i (B (i+1)):= by
   unfold precredit; rw [dif_pos hi.le,dif_pos (show i+1 ≤ N from hi),
       cal_shift C N p d _ _ (credit_int C N p d f hf (show i+1 ≤ N from hi)), credit_step C N p d f hf hi]
lemma pre_alive (h : Opened C d i p)(hi:i ≤ N)(hg: Booked C N p d f i hi) : accepted C N p d i (B i) (X i (R i)):= by
   unfold precredit Prequote; rw [dif_pos hi,dif_pos h,dif_pos hi]
   change accepted _ _ _ _ _ _ (fitting d N p i H h hi _); rw [map_smul]; unfold topReport; rw [LinearEquiv.apply_symm_apply]
   obtain ⟨a,he,hf⟩:= Literal.Booked.sheet C N p d hg; exact accepted.scale (by exact ⟨a,_,he,rfl,hf⟩) _ H h hi
lemma pre_receipt (h : Opened C d i p)(hi:k≤ N)(hg: i≤ k)(hq:Opened C d k p) :
    gMap C N p d k (measuring C d N p k (R i)) = receipt C N p d H i k h hq hg hi f:= by
   unfold Prequote; rw [dif_pos h,dif_pos (hg.trans hi)]; change gMap C N p d k (fitting d N p k H hq hi _) = _; rw [map_smul]; rfl
lemma pred_of (hg : Opened C d i p)(hi:i ≤ N)(hF: Booked C N p d f i hi)
    {b:Config G (C.side i p)→ℂ}(hx:accepted C N p d i b 0)
    (he: B i=b+W i y) : R i=y:= by
   have hz:= pre_alive C H N p d f (k:=k) hg hi hF; rw [he] at hz; apply (fitting d N p i H hg hi).injective
   exact (hz.min (accepted.combine hx (accept_cal H hg hi y) H hg hi) H hg hi).trans (zero_add _)
-- descending ordinary continuation on one-root window
lemma downward (hf:Continuous f)(hp: Opened C d i p)(hq:Opened C d (i+1) p)(hi:i<N)(he:Gate C d N p i γ 1)
    (hF:Booked C N p d f i hi.le)
    (hy: Nullity C N p d (i+1) (B (i+1)-W (i+1) (R (i+1))) D) :
    Nullity C N p d i (B i - W i (R i)) (μ₀ i*D) ∧ mCost C d N p i (R i-R (i+1)) ≤ μ₀ i*D:= by
    let y:= R (i+1); let v:= B (i+1)-W (i+1) y
    obtain ⟨z,hz,ht⟩:= nullity_toss v he hy
    have hx : B i= (τ i v-W i z)+W i (z+y):= by
        rw [cal_add d N p i H hp.post hi.le,pre_step C N p d f hf hi,← add_assoc, sub_add_cancel, factory_eq d N p i H hp.post hi y]
        have hh:= hy.message H hq.post hi; have ht:= (Ink.invest H hq hi y).message H hq.post hi
        have he : B (i+1)=v+W (i+1) y:= (sub_add_cancel ..).symm; rw [he,transition_add d N p (u:=v) hh ht]
    have hl:= pred_of C H N p d f hp hi.le hF ht.pred hx; rw [hl, hx]; rw [add_sub_cancel_right]
    change _ ∧ Y' i (z+y-y)≤ _; exact ⟨ht, (add_sub_cancel_right z y).symm ▸ hz⟩

lemma mCost_add (hp:Opened C d i p)(hi:i ≤ N)(x y:C.label d): Y' i (x+y) ≤ Y' i x+Y' i y:= by unfold mCost; rw [measuring_add _ _ _ _ H hp hi]; exact Size.add ..
lemma mCost_zero (hp:Opened C d i p)(hi:i≤N): Y' i 0=0:=by change s ((fitting d N p i H hp hi) 0)=0; rw [map_zero]; simp [Labels.Frame.coeffSize]

omit H in
lemma hike_cost (e:Region C N p d u b γ) {i j:ℕ}(hu:u ≤ i) (hi:i≤j)(hh:j ≤ b)(x:C.label d):
   mCost C d N p j x ≤ hike C i j γ * mCost C d N p i x:= by
   induction j, hi using Nat.le_induction with
   | base => simp [hike_id]
   | succ j hi ih =>
      refine le_trans ((e.cross j (hu.trans hi) hh).1 x)
        (mul_le_mul_of_nonneg_left (ih (le_trans (Nat.le_succ _) hh)) (Real.rpow_nonneg (zero_le_one.trans (factor_positive C _).le) γ) |>.trans_eq ?_)
      rw [hike_succ]; ring

lemma descended (hf:Continuous f)
    (e:Region C N p d u k γ) (hb:b≤ k)(hk:k ≤ N)
    (hy: Nullity C N p d b (B b-W b (R b)) D)
    (hF:∀ i, u≤ i → ∀ h0:i≤ b,Booked C N p d f i (h0.trans (hb.trans hk))) :
    ∀ i≥u,i≤b→ Nullity C N p d i (B i-W i (R i)) (hike C b i rate * D) := by
    intro i hh hi; induction hi using Nat.decreasingInduction with
    | self=> simpa only [hike_id,one_mul] using hy
    | of_succ i hi ih=>
      have hs:=hh.trans i.le_succ; have hq:=hi.trans_le hb
      have he:= downward C H N p d f hf (e.openGate _ hh hq.le) (e.openGate _ hs hq) (hq.trans_le hk) (e.cross i hh hq) (hF i hh hi.le) (ih hs)
      rw [hike_back, mul_assoc]; exact he.1

lemma tail (hf:Continuous f) (e:Region C N p d u k γ) (hb:b≤k)(hk:k≤N)
    (hy: Nullity C N p d b (B b-W b (R b)) D)(hF:∀ i, u≤ i → ∀ h0:i≤ b,Booked C N p d f i (h0.trans (hb.trans hk))) (hi:u≤ i)(hh:i≤b):
    mCost C d N p k (R u - R i) ≤ 2*(hike C i k γ)*(hike C b i rate *D):= by
    have hz:0≤D:=Ink.ok hy
    have hp:=e.openGate k ((hi.trans hh).trans hb) le_rfl
    induction i, hi using Nat.le_induction with
    | base=> rw [sub_self,mCost_zero C H N p d hp hk]; have he₀:= hike_pos C u k γ; have he₁:= hike_pos C b u rate; positivity
    | succ i hi ih=>
      specialize ih (Nat.le_succ _ |>.trans hh)
      let hN:= (le_trans hh hb); have hq:i< k:=hN; let x:=R i-R (i+1)
      have hT:= (downward C H N p d f hf (e.openGate i hi hq.le) (e.openGate (i+1) (hi.trans i.le_succ) hq) (lt_of_lt_of_le hq hk) (e.cross i hi hq) (hF i hi ((Nat.le_succ _).trans hh)) (descended C H N p d f hf e hb hk hy hF (i+1) (hi.trans i.le_succ) hh)).2
      have hcost : Y' k x ≤ hike C i k γ*(hike C b i rate * D):= calc
         _ ≤ _:= hike_cost C N p d e hi hq.le le_rfl x
         _ ≤ _:= mul_le_mul_of_nonneg_left (by rw [hike_back,mul_assoc]; exact hT) (hike_pos C _ _ _).le
      have he : R u - R (i+1)= (R u-R i)+x:=by unfold x; abel
      let c := t i
      refine he ▸ ?_ -- likely direction
      refine (mCost_add C H N p d hp hk _ _).trans ((add_le_add ih hcost).trans ?_)
      rw [show hike C i k γ = (factor C i)^γ * hike C (i+1) k γ from ?_, hike_back C b i]
      · have hS:= mul_le_mul_of_nonneg_right (e.cut i hi hq) (show 0≤ hike C (i+1) k γ* (hike C b (i+1) rate * D) from by have he:= hike_pos C (i+1) k γ; have hz':=hike_pos C b (i+1) rate; positivity)
        have h := show 0≤ hike C (i+1) k γ* (hike C b (i+1) rate * D) from by have he:= hike_pos C (i+1) k γ; have hz':=hike_pos C b (i+1) rate; positivity
        linarith only [h,hS]
      rw [tGap C i k,tGap C (i+1), Schedule.scale_succ,Real.rpow_def_of_pos (zero_lt_one.trans (factor_positive ..)), ← Real.exp_add]; unfold GermGraph.factor; ring_nf
omit H in
lemma regions (h:MergeProof.Ribbons.Materials C){γ:ℝ}(hγ:0<γ)(hr:γ<rate):
   ∀ᶠ j:ℕ in atTop, ∀ p N:ℕ, ∀ k:ℕ,k ≤ N → Region C N p d j k γ:= by
   obtain ⟨b,hb⟩:=eventually_atTop.mp (open_late C h.hG d)
   filter_upwards [message_graph C d h hγ zero_lt_one,eventually_ge_atTop b,factor_cap C hγ.le hr] with j hj hh ht p N k hk
   exact ⟨fun i hi _=> hb _ (hh.trans hi) _,fun i hi he=>(hj i hi _ _ (he.trans_le hk)).2, fun i hi _=>(ht i hi).2⟩
end YM.RG16.Guarding
