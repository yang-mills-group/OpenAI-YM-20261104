import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Permit
/-! # Each use of composition in the T-powers movement price

For a compact step (in the doubling chain), G.1 comparison at that **exact s,T**
including the fixed-ratio order of precision pays the substitution and composition estimate.
We index recurrence remainder from first step → new starting point s_i; telescope errors
from successive steps with at most **polynomial** growth in T (a constant amplification per step
independent of accuracy order suffices). Cf. the calculation in the text; direction
of iteration here is to peel a FIRST step, spend uniform step clock costs there. After spending high orders get sharp G.1 norm bounds separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {d : ℕ} {D : Route G}

abbrev Operator (G : Gauge) (d : ℕ) := Matrix (Toon G d) (Toon G d) ℂ
-- Beside: EXACT two-home conversion, route (frame below); use here all caps for doing any geometry
abbrev actual (D : Route G) (d : ℕ) (r T : ℝ) := columns (D r (r*T) d)

def ClockQuote (G : Gauge) (ψ : ℝ→PowerSeries ℂ) (t : ℝ→ℝ) (p : ℕ) : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ 1, T ≤ 2 →
    ‖(↑(t (r*T)):ℂ)-crop p (t r) (ψ (-Real.log T))‖ ≤ C*g0 G r^(p+1)

def FieldQuote (G : Gauge) (B : ℝ→ Frames G) (t : ℝ→ℝ) (D : Route G) (d p : ℕ) : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ 1, T ≤ 2 →
    stiffness (actual D d r T-form B d T p (t r)) ≤ C*g0 G r^(p+1)

/-- Purchase compact `[1,2]` G.1 at *all* positive orders, continuous growing theorem conditional
on this. (Can weaken to finite for individual orders by rather different scheme.) -/
structure StepCost (G : Gauge) (ψ : ℝ→PowerSeries ℂ) (B : ℝ→Frames G) (t : ℝ→ℝ) (D : Route G) : Prop where
   clock (m : ℕ) : ClockQuote G ψ t (m+1)
   fields (d m : ℕ) : FieldQuote G B t D d (m+1)

local notation "unitₛ" => g0 G
local notation "late" => 𝓝[>] (0:ℝ)
local notation "μ" x:max => (-Real.log x)
local notation "doubles" => (2:ℝ)
variable (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[late] (g0 G))
    {a b : ℝ} {I : Type*} {X : Filter I} {r s T : I→ℝ} {k : ℕ}
    (live : Tendsto r X late) (trip : ∀ᶠ i in X, permit G a b (r i) (s i) (T i))

lemma step_cost_aux (hT : ∀ᶠ i in X,1≤T i) (Hs : Tendsto s X late) (hb : ∀ᶠ i in X, T i ≤ 2)
    (qR : ClockQuote G R t k) (qB : FieldQuote G B t D d k) (hG : G.Simple) :
    (fun i => (↑(t (s i*T i)):ℂ)-crop k (t (s i)) (R (μ(T i)))) =O[X] (fun i => unitₛ (s i) ^ (k+1)) ∧
    (fun i=> stiffness (actual D d (s i) (T i)-form B d (T i) k (t (s i)))) =O[X] (fun i => unitₛ (s i) ^ (k+1)) := by
  obtain ⟨C,hC,H⟩:= qR; obtain ⟨L,hL,P⟩:= qB
  have u:= (hT.and hb).and (now ((pace hG).comp Hs))
  constructor
  · refine IsBigO.of_bound C ?_; filter_upwards [u,Hs.eventually H] with i ⟨⟨a,b⟩,c⟩ h; change 0 < g0 G (s i) at c; exact (h _ a b).trans_eq (by rw [Real.norm_of_nonneg (pow_nonneg c.le _)])
  refine IsBigO.of_bound L ?_; filter_upwards [u,Hs.eventually P] with i ⟨⟨a,b⟩,c⟩ h; change 0 < g0 G (s i) at c; rw [Real.norm_of_nonneg (stiffPos _),Real.norm_of_nonneg (pow_nonneg c.le _)]; exact h _ a b

-- fixed amplification, buy radius sufficiently small (true step; independent of all later p)
include ht hG
lemma amplifier (u : ClockQuote G R t 1) (v : FieldQuote G B t D d 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ r in late, stiffness (actual D d r 2) ≤ C := by
  have h := (step_cost_aux (X:=late) (Eventually.of_forall fun _=> show 1 ≤ doubles by norm_num) tendsto_id
    (Eventually.of_forall fun _=> le_rfl) u v hG).2
  have t0:= ht.trans_tendsto (g0_zero hG)
  have H : (fun i=>stiffness (actual D d i 2)) =O[late] fun i=> (1:ℝ) := by
    refine matrixPay.mpr fun b c=>?_
    have h0:= matrixPay.mp h b c
    have hz : Tendsto (fun i : ℝ=> actual D d i 2 b c) late
        (𝓝 (form B d 2 1 0 b c)) := by
      have e : Continuous fun t : ℝ=> form B d 2 1 t b c := by simp_rw [form,crop_apply]; fun_prop
      have V := (e.tendsto 0).comp t0
      apply Tendsto.congr (fun i : ℝ=> sub_add_cancel (actual D d i 2 b c) (form B d 2 1 (t i) b c))
      rw [← zero_add (form B d 2 1 0 b c)]
      exact (h0.trans_tendsto (by simpa only [id_eq, zero_pow (by norm_num : (1+1:ℕ)≠0)] using (g0_zero hG).pow (1+1:ℕ))).add V
    exact isBigO_const_of_tendsto hz one_ne_zero
  obtain ⟨K,hK,H⟩:= H.exists_pos
  exact ⟨max 1 K,le_max_left ..,H.bound.mono fun i h=> (show stiffness _ ≤ K from by simpa only [Real.norm_of_nonneg (stiffPos _),norm_one,mul_one] using h).trans (le_max_right ..)⟩

include H live trip
local notation "w" => fun i:I=> T i/2
local notation "Y" => fun i:I=> s i*2
local notation "g" => fun i:I=> unitₛ (r i)
local notation "R'" => (fun i:I => R (μ(w i)))
local notation "A" => (fun i:I => form B d (w i) k (t (Y i)))
variable (hT : ∀ᶠ i in X, 2 ≤ T i) (qR : ClockQuote G R t k) (qB : FieldQuote G B t D d k)
include hT
omit H ht in
lemma journey : Tendsto Y X late ∧
    ∀ᶠ i in X, permit G a b (r i) (Y i) (w i) := by
  have e := ((live.eventually self_mem_nhdsWithin).and (trip.and hT)).mono fun i h=>(splits h.2.1 h.1 h.2.2).2
  exact ⟨(corridor hG live e).1,e⟩

include qR qB
lemma reports : Fare w X (fun i=> g i^(k+1)) (fun i=>crop k (t (Y i)) (R' i)-crop k (t (s i)) (R (μ(T i)))) ∧
    Fare w X (fun i=> g i^(k+1)* w i^d) (fun i=> stiffness (actual D d (s i) 2 * A i-form B d (T i) k (t (s i)))) := by
  let ws : I→ℝ := w; let s' : I→ℝ:= Y
  have e := journey hG live trip hT; have y := corridor hG live trip
  have Hw : ∀ᶠ i in X, 1 ≤ ws i := e.2.mono fun i h=>h.2.1
  have hp := (step_cost_aux (Eventually.of_forall fun _=>show 1 ≤ doubles by norm_num) y.1 (Eventually.of_forall fun _=>le_rfl) qR qB hG)
  have ha := (ht.comp_tendsto y.1 |>.trans y.2.1)
  have fees := hp.1.trans (y.2.1.pow (k+1)); have funds := hp.2.trans (y.2.1.pow (k+1))
  have near : ∀ᶠ i in X, |t (s' i)| ≤ 1 := (ht.trans_tendsto (g0_zero hG)|>.comp e.1 |>.abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)|<1))
  have hs : ∀ᶠ i in X, |t (s i)| ≤ 1 := (ht.trans_tendsto (g0_zero hG)|>.comp y.1 |>.abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)|<1))
  have hl : ∀ᶠ i in X, μ(T i)=μ doubles+μ(ws i) := hT.mono fun i h=>by dsimp only [ws]; rw [Real.log_div (by linarith) (by norm_num)]; ring
  let p := R (μ doubles)
  have tune : Tunes ws X (fun _=>1) (fun _=>p) := fun _=> Fare.constant _
  have root : Rooted p := H.led (μ doubles) |>.start
  constructor
  · have Hr : Tunes ws X (fun _=>1) R' := by
      intro n; have h : Rhythm (fun i:ℝ=> coeff n (R i)) := Rhythm.unit.mpr (H.smooth n)
      apply rhythm_log (f:=fun j=> coeff n (R (-j))) Hw; simpa only [Polynomial.eval_neg,Polynomial.eval_X] using h.pre (-(Polynomial.X : Polynomial ℝ))
    refine ((clock_inserting Hw hs ha tune Hr (fun i=> root) k near (Fare.bare fees)).congr ?_).extend ?_
    · filter_upwards [hl] with i h; rw [h,(H.additive ..).1]
    exact Eventually.of_forall fun i=> mul_one _
  have ht (b c: Toon G d) : Tunes ws X (fun i=>ws i^d) (fun i=> badge B (μ(w i)) (theory c) b) := by
    intro n; refine (badge_cost H Hw _ _ n).transport (IsBigO.of_bound' ?_)
    filter_upwards [Hw] with i h; simp only [norm_pow]; exact pow_le_pow_right₀ (h.trans (le_abs_self _)) (size_le _)
  refine stiffPay Hw fun b c=>?_
  let F (j : Toon G d) i := badge B (μ(ws i)) (theory c) j
  let U (j : Toon G d) := badge B (μ doubles) (theory j) b
  let rBE j i := crop k (t (s i)) (U j*((F j i).subst p))
  let pred j i := A i j c
  let val j i := actual D d (s i) 2 b j
  let pay j i := crop k (t (s i)) (U j)
  have cp (j : Toon G d) : Fare ws X (fun i=> g i^(k+1)*ws i^d) (fun i=> val j i * pred j i - rBE j i) := by
    have hz := ht j c
    have uh : Tunes ws X (fun _=>1) (fun _=>U j) := fun _=> Fare.constant _
    have u := Tunes.overflow Hw hs ha k uh (submitted Hw tune hz fun _=>root)
    have e := (Fare.cover (Tunes.cuts Hw hs k uh) (clock_inserting Hw hs ha tune hz (fun i=> root) k near (Fare.bare fees)))
    have m := ((Fare.bare (matrixPay.mp funds b j)).mul (Tunes.cuts Hw near k hz))
    refine (Fare.add Hw m (Fare.add Hw e (u.extend ?_))).congr ?_
    exact Eventually.of_forall fun _=>by simp
    exact Eventually.of_forall fun i=>by dsimp only [val,pred,Matrix.sub_apply]; unfold form rBE F U p; rw [sub_mul,mul_sub]; abel
  refine (Fare.sum Hw (fun j (_:j∈(Finset.univ:Finset (Toon G d)))=> cp j)).congr ?_
  filter_upwards [hl] with i h
  rw [Matrix.sub_apply,Matrix.mul_apply]
  change _=_-crop k (t (s i)) (badge B (μ(T i)) (theory c) b); rw [h,column_composition H, map_sum,Finset.sum_sub_distrib]
end YM.FVA2.GradedFar259.ScaleCost
