import YM.IterationFour.Vacuum.Mint
import YM.UVExtension.Oasis.Flora

/-!
# Paying exact per-level inequalities from rate inputs, continued

The source along a fixed common trajectory must supply these prices. Geometry
and particular width for reset checked here on the very same family as the UV
provider. No uniform sharp-L bill pulled from a different existential Family.

One implementation route is `Slim` schedules: upload arbitrarily large profile
fees before B but make block lengths/legal smooth indices slow enough over each
admitted tail to ensure these prices at the requested orders. Reserve in K is
needed at every step; the early K output bounds must include slack relative to
next K goal, so `forceGoal` choices matter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum.Financed
open Lattice Wilson RG Function MeasureTheory Filter Currency Render Spending
open AnalyticBridge VerifiedReset Mint
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {r : ℕ}
open Address

lemma renew_geo (hg : G.Simple) (h : YM.UVExtension.Oasis.Floral (hG:=hg) C) (m : ℕ) :
    WilsonStartup.Decent (C.path.levels.params m).clip (C.path.levels.budget m) ∧
      Geo.Width (C.path.levels.budget m) (C.path.levels.params m).clip (C.path.levels.params m).width := by
  obtain ⟨M,P,A,R,S,T,t,K,w,Q,L,H,rfl,_⟩:= h
  have hz:= UVExtension.Guild.hp_width (m:=m) (N:=m+1) (n:=0) R (Nat.lt_succ_self m)
    (((UVExtension.Mast.Cellar.yard (UVExtension.Mast.roseA S) L).path.rep (m+1) 0 (m+1)))
  exact hz

def eligible (D : Set ℕ) (A : Address) := A.period∈D ∧ A.level≤A.top
abbrev tenor (D : Set ℕ) := pass (eligible D)
abbrev fare (a : Levels G) (D : Set ℕ) := Account a Address.level (tenor D)
lemma warm (D : Set ℕ) : Tendsto Address.level (tenor D) atTop := at_tail ..
lemma bright (D : Set ℕ) : ∀ᶠ i in tenor D, eligible D i := okay ..
variable (t : ℕ→ℕ→ℕ→Pocket)
def fees (A : Address) := t A.top A.period A.level

variable {I : Type*} {m : I→ℕ} {L : Filter I} {a : Levels G}
open Series
lemma levy_slim (hg : G.Simple) (he : Tendsto m L atTop) {f : I→ℝ} (hx : Account a m L f 0) (k : ℕ) :
    Account a m L (fun i=> levy (f i) k) 0 := by
  induction k with
  | zero=> exact Account.constant hg he a 1
  | succ k ih=>
    have hh:Account a m L (fun i=> levy (f i) k ^2*f i) 0:=by
      simpa using! ((ih.repeatOrder hg he 2).product hx)
    have ht := ih.joint hg he (show Account a m L (fun i=> (levy (f i) k ^2*f i+1)*((2:ℝ)⁻¹)) 0 from
        add_zero (0:ℝ) ▸ ((hh.joint hg he (Account.constant hg he a 1)).product
          (Account.constant hg he a (2:ℝ)⁻¹)))
    simpa only [levy, div_eq_mul_inv] using ht

variable (D : Set ℕ) (P : (N q : ℕ)→ Plan C N q r)
def modelCharge (A : Address) := ∑ e∈Finset.range (r-2+1), |(P A.top A.period).coefficient A.level e|
def up (A : Address) : Prop := eligible D A ∧ A.level < A.top
lemma active : pass (up D) ≤ tenor D := inf_le_inf_left _ (principal_mono.mpr (by exact fun _ hv=> hv.1))
variable {D P}

lemma validPrediction (hg : G.Simple) (ht : C.Makes)
    (hf : fare C.path.levels D (modelCharge P) 0) : ∀ᶠ i in tenor D,
        (P i.top i.period).predict i.level ∈ stripe (B C.path.levels i.level) := by
  let a:=C.path.levels
  have hz := hf.order hg (warm D) (show (-2:ℝ) < 0 by norm_num) (show 0<(1/8:ℝ) by norm_num)
  obtain ⟨k,hk⟩:= eventually_atTop.1 (g_small hg ht 1 zero_lt_one)
  filter_upwards [hz,bright D,(warm D).eventually_ge_atTop k,
    (warm D).eventually (adjacent a hg (3/2) (by norm_num))] with i hi hv hw hp
  by_cases hu:i.level=i.top
  · rw [Plan.predict, if_pos hu]; exact actual_band ht _ _ _ hv.2
  let j:= i.level; let N:=i.top; let q:=i.period
  let y:=g C N q (j+1); let β:=B a j
  have hy : j+1≤ N:= lt_of_le_of_ne hv.2 hu
  have hY:y ≤ 1:= (hk _ (hw.trans (Nat.le_succ j)) N q hy).le
  have hx:0≤ y:= le_of_lt (g_pos ht N q _ hy)
  let T:=P N q
  have hh: |T.poly j y| ≤ β/8:= calc
    _ ≤ modelCharge P i := by
      unfold Plan.poly; apply (Finset.abs_sum_le_sum_abs ..).trans
      unfold modelCharge; refine Finset.sum_le_sum fun l _=> ?_
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx _)]; exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx hY)
    _ ≤ _ := by
      have h:weight a (-2) j=β:= by
        have hx:=weight_add a j 2 (-2)
        rw [weight_two] at hx
        change _=(β:ℝ)⁻¹* _ at hx
        rw [add_neg_cancel, Currency.weight,Real.rpow_zero] at hx
        have hb: β ≠ 0:= (WardBin.hot a j).ne'
        field_simp [hb] at hx; linarith
      change |modelCharge P i| ≤ (1/8:ℝ)*weight a (-2) j at hi
      rw [h] at hi; linarith only [hi, le_abs_self (modelCharge P i)]
  have h0:0<β:= WardBin.hot a j
  obtain ⟨hl,he⟩:= abs_le.mp hh
  obtain ⟨hb₁,hb₂⟩:= (ht.wilson.represents _ q _ hy).band
  have hs:β ≤ B a (j+1):= YM.Push.Corrected.Last.band_le a hg (Nat.le_succ j)
  change B a (j+1) ≤ _ * β at hp
  change B a (j+1) / 2 ≤ _ at hb₁
  change _ ≤ 2*B a (j+1) at hb₂
  rw [Plan.predict, if_neg hu]
  change β/4 ≤ C.path.β N q (j+1)+T.poly j y ∧ C.path.β N q (j+1)+T.poly j y ≤ 4*β
  constructor <;> linarith only [hl,he,h0,hs,hp,hb₁,hb₂]

lemma ticket_income (hg : G.Simple) (ht : C.Makes) (Y : Purse) (hs : Y.sigma < (r:ℝ)+1)
    (hf : fare C.path.levels D (modelCharge P) 0) : Ticket D Y r P := by
  let a:=C.path.levels; let L:=pass (up D); let d i:=direction (P (top i) (period i)) (level i); let R i:=root (d i) r
  have h:= at_tail (up D)
  have he : Account a level L (fun i=> Series.mass (d i)) 0 := by
    apply Account.relax ((Account.constant hg h a 1).joint hg h (hf.restrict (active D)))
    exact Eventually.of_forall fun i=> by rw [abs_of_nonneg (mass_nn ..)]; exact (direction_cost ..).trans (le_abs_self _)
  have hp : Account a level L (fun i=> mass (R i)) 0 := by
    apply Account.relax (levy_slim hg h he r)
    exact Eventually.of_forall fun i=>by rw [abs_of_nonneg (mass_nn ..)]; exact (mass_cost le_rfl r).trans (le_abs_self _)
  let U (i:Address):= g C i.top i.period (i.level+1)
  have hU : Account a level L U 1 := by
    apply Account.absoluteEdge hg h
    refine ⟨2,zero_lt_two,?_⟩
    filter_upwards [okay (up D)] with i hi
    unfold Currency.weight
    rw [Real.rpow_one,abs_of_pos (show 0<U i from g_pos ht i.top i.period (i.level+1) hi.2)]
    apply le_trans ((hat_g ht i.top i.period (i.level+1) hi.2).2) (mul_le_mul_of_nonneg_left ?_ zero_le_two)
    exact inv_anti₀ (Real.sqrt_pos.2 (WardBin.hot ..)) (Real.sqrt_le_sqrt (YM.Push.Corrected.Last.band_le a hg (Nat.le_succ _)))
  have hy: Account a level L (fun i=> (mass (R i)+1)*U i) 1 := by simpa using (hp.joint hg h (Account.constant hg h a 1) |>.product hU)
  have ht' : Account a level L (fun i=> mass (Series.equation (d i) (R i))) 0:= by
    have he : Account a level L (fun i=> mass (R i)^2 * mass (d i) +1) 0:= by
      refine Account.joint hg h ?_ (Account.constant hg h a 1)
      simpa using! ((hp.repeatOrder hg h 2).product he)
    refine he.relax <| Eventually.of_forall fun i=>?_
    rw [abs_of_nonneg (mass_nn ..)]
    exact (equation_cash ..).trans (le_abs_self _)
  have hv: Account a level L (fun i=> 128*mass (Series.equation (d i) (R i))*U i^(r+1)) ((r:ℝ)+1) := by
    simpa using! (((Account.constant hg h a 128).product ht').product (hU.repeatOrder hg h (r+1)))
  have hp := (hy.vanishing hg h zero_lt_one (1/2) (by norm_num)).and (hv _ hs)
  filter_upwards [(pass_iff (up D) _).1 hp] with i hi N q hQ hm
  obtain ⟨hS,hT⟩:= hi N q ⟨⟨hQ,hm.le⟩,hm⟩
  exact ⟨(le_abs_self _).trans hS,(le_abs_self _).trans hT⟩


/-- Remaining inputs on unmarked schedule. More convenient grades (3 for
    unitBill, any margin here >11/5 suffices), keeping C of δ/b before L. -/
structure Booking (hg : G.Simple) (D : Set ℕ) (Y : Purse) (P : (N q : ℕ)→ Plan C N q r)
    (ν : ℝ) (v : ℕ) : Prop where
    holo : YM.UVExtension.Oasis.Floral (hG:=hg) C
    slow : Slow C.path.levels
    entries : ∀ᶠ i in tenor D, (fees t i).forceGoal > 0
    demand : ∀ᶠ i in tenor D, (fees t i).forceEarly ≥ 0 ∧ (fees t i).forceGoal ≤ C.path.levels.clock.forcedAllowance i.level
    masks : Account C.path.levels Address.level (tenor D) (fun i=> (fees t i).forceEarly/(fees t i).forceGoal) 1
    reset_terms : fare C.path.levels D (modelCharge P) 0
    reset_alpha : fare C.path.levels D (fun i=> (P i.top i.period).alpha i.level) 0
    printed : ∀ᶠ (i : Address) in tenor D,
      permits ((P i.top i.period).layers i.level) (C.path.levels.budget i.level) ∧
      ∀ (w : Piece G (C.side i.level i.period)), w ∈ (P i.top i.period).layers i.level → w.rank ≤ v
    first : fare C.path.levels D (fun i=> unitBill ((P i.top i.period).layers i.level) (B C.path.levels i.level)) 3
    funds : fare C.path.levels D (fun i=> (fees t i).single) ν
    older : fare C.path.levels D (fun i=> (fees t i).response) 0
    gains : ∀ᶠ i in tenor D, (2+adjusting C.path.levels i.level)*(fees t i).repeatCost ≤ Y.theta

end YM.IterationFour.Vacuum.Financed
