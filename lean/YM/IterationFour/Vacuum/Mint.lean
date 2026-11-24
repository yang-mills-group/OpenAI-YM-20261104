import YM.IterationFour.Vacuum.Tail
import YM.IterationFour.Spending

/-!
# Paying exact per-level inequalities from rate inputs

FG computations submit e.g. `taylor`, `transport` buys with *all* their
polynomial-of-geometry losses. Provide scalar gates in a way implementable
in one actual schedule. `Slim` conditions are post-L; we'll consider paying
them by prolonging delay. The inherited rate multiplier with the pre-L
coefficient, however, must be chosen to give a strict gate BEFORE that -- not
calling a subpower quantity a contraction. All-order Φ-schedule requires
still choosing lengths to meet each finite list.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum.Mint
open Lattice Wilson RG Function MeasureTheory Filter Currency Render Spending
open AnalyticBridge VerifiedReset Collection
open scoped Topology BigOperators ContDiff
variable {G : Gauge}
open Address

lemma price_rank {n : Side} (S : List (Piece G n)) {p : BudgetPoint} (h : permits S p) {K : ℝ}
    (hk : ∀ w∈S, tiltFee (stepOrder w) ≤ K*gainFee (stepOrder w)) (b : ℝ) (hb : 0<b) :
    shiftBill S b * b ≤ K * unitBill S b := by
  induction S with
  | nil => simp [unitBill,shiftBill,dollars]
  | cons s l ih=>
      have hl := ih (seated h) (fun u hu=> hk u (List.mem_cons_of_mem _ hu))
      have ht:= Payload.nonneg (Render.first h)
      have hx:= mul_le_mul_of_nonneg_right (hk s List.mem_cons_self)
        (mul_nonneg (show 0≤ (gain b)^(stepOrder s) by unfold gain; positivity) ht)
      unfold unitBill shiftBill; rw [dollars,dollars,add_mul,mul_add]; apply add_le_add _ hl
      refine Eq.trans_le ?_ (le_trans hx ?_)
      · field_simp
      exact Eq.le (by ring)
lemma rank_bill (r n : ℕ) : ∃ K:ℝ,0≤K ∧ ∀ {u : Side} (S : List (Piece G u)) (A : BudgetPoint) (x:ℝ),
    0<x → (∀ w∈S,w.power≤r ∧ w.rank≤n) → permits S A → shiftBill S x*x≤K*unitBill S x := by
  classical
  let p (x y:ℕ) := tiltFee ((x:ℝ)-y)/gainFee ((x:ℝ)-y)
  let K := ∑ x∈Finset.range (r+1), ∑ y∈Finset.range (n+1), p x y
  have h x y:0≤p x y:=div_nonneg (tiltFee_nonneg _) (gainFee_pos _).le
  have hg x:0≤ ∑ y∈Finset.range (n+1), p x y:= Finset.sum_nonneg fun y _=> h x y
  refine ⟨K,Finset.sum_nonneg fun x _=> hg x,fun S _ x he hv hp=>?_⟩
  apply price_rank S hp _ x he; intro w hw
  obtain ⟨hx,hy⟩:= hv w hw
  unfold stepOrder; push_cast; apply (div_le_iff₀ (gainFee_pos _)).1
  exact (Finset.single_le_sum (s:=Finset.range (n+1)) (fun y _ => h w.power y)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hy))).trans
      (Finset.single_le_sum (fun x _=> hg x) (Finset.mem_range.mpr (Nat.lt_succ_of_le hx)))

/-- Pay projections already in `Room.pays`, not reconstructed later. -/
structure Slow (a : Levels G) : Prop where
    pre : Slip a (fun i=> adjusting a i)
    beam : Slip a (fun i=> Time.softCeiling G (a.params i) 1)

/-- Use strong exponent of marker-free compulsory outputs. -/
lemma send_rate (a : Levels G) (i : ℕ) {γ w C : ℝ} (hK : 0 < γ) (hv : γ ≤ a.clock.forcedAllowance i) (hp : 0≤w)
    (hx : 0≤C)
    (hc : let p := a.budget i; (p.B+p.B+1:ℕ)^4*(w/γ+2*C) ≤ (1:ℝ)/4) : Progress.DirectedRecipe.Payments.Rates (a.budget i).B γ w C (-Real.log γ) := by
  let k:=-Real.log γ
  have hh : Real.exp (-k)=γ:= by unfold k; rw [neg_neg,Real.exp_log hK]
  let Y:=w/γ+2*C; let X:= Progress.DirectedRecipe.Payments.inflation w C k
  have hy : X=Y:=by unfold X Progress.DirectedRecipe.Payments.inflation k; rw [Real.exp_neg, Real.exp_log hK, inv_mul_eq_div]
  have hn:0 ≤ X:=by rw [hy]; unfold Y; positivity
  have h' := hc
  let b:=a.budget i
  change (b.B+b.B+1:ℕ)^4*Y ≤ (1:ℝ)/4 at h'
  rw [← hy] at h'
  have hl : X ≤ 1/4:= (le_mul_of_one_le_left hn (show (1:ℝ) ≤ ((b.B+b.B+1:ℕ):ℝ)^4 from by exact_mod_cast Nat.succ_le_of_lt (pow_pos (show 0<b.B+b.B+1 by omega) 4))).trans h'
  refine ⟨?_,hp,hx,?_,?_,?_⟩
  · apply neg_nonneg.mpr (Real.log_nonpos hK.le (hv.trans _)); exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  · rw [hy] at hl; unfold Y at hl; linarith [div_nonneg hp hK.le]
  · exact h'.trans (by norm_num)
  change Real.exp (-k)*(Real.exp X-1) ≤ γ; rw [hh]
  have hg := Real.abs_exp_sub_one_le (x:=X) (by rw [abs_of_nonneg hn]; linarith)
  rw [abs_of_nonneg hn] at hg
  exact mul_le_of_le_one_right hK.le (by linarith [(abs_le.mp hg).2])

lemma send (a : Levels G) (i : ℕ) {α H γ w C : ℝ} (hK : 0 < γ) (hv : γ ≤ a.clock.forcedAllowance i) (hp : 0≤w)
    (he : softNeed G (a.budget i) (a.params i).clip (a.params i).width (a.params i).paths α H ≤ C) (hx : 0≤C)
    (hc : let p := a.budget i; (p.B+p.B+1:ℕ)^4*(w/γ+2*C) ≤ (1:ℝ)/4) : Duty a i α H w γ :=
    ⟨C,-Real.log γ,he,send_rate a i hK hv hp hx hc⟩

lemma soft_pos (a : Levels G) (i : ℕ) (u : ℝ) (hu : 0≤u) : 0≤ Time.softCeiling G (a.params i) u:= by
  let p:=a.params i
  have h:= Time.soft_pos G p
  have hv:= (budget_pos (Time.probe p) G p.clip p.width_pos p.paths_pos.le).2.2
  have ht:= pair_nonneg G (Time.probe p)
  unfold Time.softCeiling
  change 0≤ Quotes.softReset G _ _ + (_ + 2⁻¹*pairBill G (Time.probe p))*Quotes.lowHard (Time.probe p) p.clip p.width p.paths
  positivity

lemma soft_rate {I : Type*} (hg : G.Simple) (a : Levels G) (h : Slow a) {i : I→ℕ} {L : Filter I} (he : Tendsto i L atTop)
    {f : I→ℝ} (hp : Account a i L f 0) : Account a i L (fun u=> Time.softCeiling G (a.params (i u)) (|f u|)) 0 := by
  let x u:= |f u|
  have hb : Account a i L (fun u=> Time.softCeiling G (a.params (i u)) 1) 0 := Account.gathered i he h.beam
  have hx : Account a i L x 0:=hp.unsigned
  let g u:=(x u+1)*Time.softCeiling G (a.params (i u)) 1
  have ht : Account a i L g 0:= ((hx.joint hg he (Account.constant hg he a 1)).product hb)|> (zero_add (0:ℝ) ▸ ·)
  refine ht.relax (Eventually.of_forall fun u=>?_)
  let p:=a.params (i u)
  have hq:= Time.soft_pos G p
  have hy:= (budget_pos (Time.probe p) G p.clip p.width_pos p.paths_pos.le).2.2
  have hW:= pair_nonneg G (Time.probe p)
  have hz : 0≤ x u:=abs_nonneg _
  change |Time.softCeiling G p _| ≤ |g u|
  rw [abs_of_nonneg (soft_pos a (i u) (x u) hz)]; apply le_trans ?_ (le_abs_self (g u))
  change Time.softCeiling G p (x u) ≤ (x u+1)*Time.softCeiling G p 1
  unfold Time.softCeiling
  rw [mul_add]
  apply add_le_add
  · exact le_mul_of_one_le_left hq (by linarith)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by nlinarith) hy
end YM.IterationFour.Vacuum.Mint
