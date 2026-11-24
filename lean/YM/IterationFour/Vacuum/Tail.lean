import YM.IterationFour.Vacuum.Adjacent

/-!
# Tail-uniform unmarked comparison (conditional theorem)

Arbitrary fixed order ≥2. Uniform in ALL cutoff/periods IN THE DOMAIN of the
local estimates. This module and the adjacent ones do not assert those new
(local, pointwise/norm) estimates, nor choose the Plans. Explicit induction
on the *actual* unnormalized density, all levels m through N, preserves the
representation with the proof of output generation needed for the next step.
Trailing (below m) low-order thresholds not touched. Actual beta trajectory
is never identified with the hypothetical central schedule, a fitted analytic
curve, or the finite series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function MeasureTheory Filter Currency
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G}

/-- Not all m<l have their collars; quantify over an arbitrary period set
    `D` on which the supplied local hypotheses hold. Application must still
    instantiate them on the WHOLE required domain. -/
structure Entrance (D : Set ℕ) (Y : Purse) (r : ℕ) (P : (N q : ℕ)→ Plan C N q r) (t : ℕ→ℕ→ℕ→Pocket) : Prop where
    budgets : ∀ᶠ i:ℕ in atTop,∀ N q, q∈D → i≤N → Room C Y (P N q) i (t N q i)
    localSteps : ∀ᶠ i:ℕ in atTop,∀ N q, q∈D → i≤N → Counter (P N q) Y (t N q) i

lemma tail (hg : G.Simple) (ht : C.Makes) {D : Set ℕ} {Y r P t} (h : Entrance (C:=C) D Y r P t) :
    ∀ᶠ m:ℕ in atTop,∀ N q, q∈D → m≤N → ∃ L, Aligned (P N q) Y (t N q) m L := by
  obtain ⟨j,hj⟩:= Filter.eventually_atTop.1 h.budgets
  obtain ⟨k,hk⟩:= Filter.eventually_atTop.1 (waves hg ht Y.w)
  filter_upwards [h.localSteps,eventually_ge_atTop j,eventually_ge_atTop k] with m hm hz hv N q hp hN
  exact traced _ _ hg ht (hm N q hp hN) hN (fun i hi he=> hj i (hz.trans hi) N q hp he) (fun i hi _=> hk i (hv.trans hi))

/-- Two additional explicit finite coefficient demands, at the level's gamma.
    Can be paid easily with the coefficients estimated at the right rates and
    the schedule. Spends the *printing* order r, not the actual sigma with
    eta loss, in the Taylor tail. -/
def Ticket (D : Set ℕ) (Y : Purse) (r : ℕ) (P : (N q : ℕ)→ Plan C N q r) : Prop :=
    ∀ᶠ i:ℕ in atTop, ∀ N q, q∈D → i<N →
    let u:=g C N q (i+1); let d:=direction (P N q) i; let R:=Series.root d r
    (Series.mass R + 1)*u ≤ 1/2 ∧ 128*Series.mass (Series.equation d R)*u^(r+1) ≤ weight C.path.levels Y.sigma i

def movement (Y : Purse) := (ratioConstant Y+1)*(2:ℝ)^Y.sigma

/-- Converted bounds on this ONE aligned trace. No phase choice needed in
    these unmarked finite regulator statements. Stages outside `[m,N]` aren't
    updated. `gamma` as supplied by Counter (not inferred from rank). -/
structure Purchase (N q m : ℕ) (Y : Purse) (r : ℕ) (P : Plan C N q r) (t : ℕ→Pocket) (L : Trail (C:=C) (q:=q)) : Prop where
    stocks (i:ℕ)(hi:m ≤ i)(hx:i≤N): Issued P Y t i (L.loss i) (L.atLevel i)
    errors (i : ℕ) (hm : m≤ i) (hi : i≤N) : Coin C N q i (P.layers i) (L.atLevel i)
      ((Y.fare*(2:ℝ)^Y.sigma) * (g C N q i)^Y.sigma) (t i).forceGoal (Y.guardBill C.path.levels i)
    steps (i : ℕ) (hm : m ≤ i) (hi : i<N) :
      |C.path.β N q i-C.path.β N q (i+1)-P.poly i (g C N q (i+1))| ≤
        ((Y.fare+1)*(2:ℝ)^(Y.sigma-2)) * (g C N q i)^(Y.sigma-2) ∧
      let u:=g C N q (i+1)
      |g C N q i/u-Polynomial.eval u (Series.root (direction P i) r)| ≤ movement Y * (g C N q i)^Y.sigma

lemma Purchase.sub {N q m Y r t j} {P : Plan C N q r} {L: Trail (C:=C) (q:=q)} (h : Purchase N q m Y r P t L) (hm:m ≤ j): Purchase N q j Y r P t L:=
    ⟨fun i hi hx=> h.stocks i (hm.trans hi) hx,fun i hi hx=> h.errors i (hm.trans hi) hx,fun i hi hx=> h.steps i (hm.trans hi) hx⟩
structure Obtains (N q m : ℕ) (Y : Purse) (r : ℕ) (P : Plan C N q r) (t : ℕ→Pocket) (L : Trail (C:=C) (q:=q)) : Prop extends Purchase N q m Y r P t L where
    journal : Aligned P Y t m L

/-- Ratio price consequence OVER SAME purchased output state.
    Needs only numeric prediction stripe and certificate in Brief. This
    generality used in Shore route and when applying the RMS receipt
    after having issued an Aligned witness. -/
theorem shopping (hg:G.Simple) (ht:C.Makes) {D} {Y : Purse} {r:ℕ} {P : (N p:ℕ)→ Plan C N p r} {t : ℕ→ℕ→ℕ→Pocket} (hr : 2≤r) {η : ℝ} (he: 0<η ∧ η<1/2) (hY:Y.sigma=(r:ℝ)+1-η) (hp: Ticket (C:=C) D Y r P) (hb:∀ᶠ i:ℕ in atTop,∀ N p,p∈D → i<N → (P N p).predict i∈stripe (B C.path.levels i)) :
    ∀ᶠ m : ℕ in atTop,∀ N p,p∈D → ∀ L:Trail (C:=C) (q:=p),
      (∀ i, m ≤ i→ i ≤ N → Issued (P N p) Y (t N p) i (L.loss i) (L.atLevel i)) → Purchase N p m Y r (P N p) (t N p) L:=by
  obtain ⟨j,hj⟩:= eventually_atTop.1 hb
  obtain ⟨k,hk⟩ := eventually_atTop.1 hp
  obtain ⟨l,hl⟩ := eventually_atTop.1 (g_small hg ht 1 zero_lt_one)
  obtain ⟨v,hv⟩ := eventually_atTop.1 (adjacent C.path.levels hg 4 (by norm_num))
  filter_upwards [eventually_ge_atTop j,eventually_ge_atTop k,eventually_ge_atTop l,eventually_ge_atTop v] with m h1 h2 h3 h4 N q hD L hL
  refine ⟨hL,fun i hm hi=>?_,fun i hm hi=>?_⟩
  · have hI:=hL i hm hi
    refine hI.coupon.enlarge (hI.cap.trans ?_)
    unfold Purse.limit; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((g_weight ht (N:=N) (q:=q) hi _ Y.above).1) Y.cash.le
  let a:=C.path.levels
  have hI:= hL i hm hi.le
  have hz : 0 ≤ Y.sigma-2 := by
    have hh : (2:ℝ) ≤ r:= by exact_mod_cast hr
    linarith only [hY, hh, he.2]
  obtain ⟨hp,hk⟩:= hk i (h2.trans hm) N q hD hi
  constructor
  · calc
      _ = |(P N q).predict i-C.path.β N q i| := by rw [abs_sub_comm ((P N q).predict i),sub_sub,Plan.predict,if_neg hi.ne]
      _ ≤ _ := hI.kinetic
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((g_weight ht (N:=N) (q:=q) hi.le _ hz).1) (by linarith only [Y.cash])
  intro u
  calc
    _ ≤ _ := radius (P N q) hg ht Y i hi (hj i (h1.trans hm) N q hD hi) hI (hv _ (h4.trans hm))
      (hl (i+1) ((h3.trans hm).trans i.le_succ) N q hi).le hp
    _ ≤ (ratioConstant Y + 1) * weight a Y.sigma i := (add_le_add_right hk _).trans_eq (by dsimp only [a]; ring)
    _ ≤ _ := by unfold movement; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((g_weight ht (N:=N) (q:=q) hi.le _ Y.above).1)
                  (by linarith only [ratioConstant_nn Y])

/-- β error thus relative order r+1-η when multiplying a quadratic in g (remember
    losing two powers), and with the ratio error in actual couplings the next
    dilation can request precisely this convention. The sigma gate for E
    allowance needs to be in Entrance. Constants may depend arbitrarily on r
    and η; no common infinite-order radius is asserted. -/
theorem charging (hg : G.Simple) (ht : C.Makes) {D Y r P t} (hr : 2≤r)
    {η : ℝ} (he : 0 < η ∧ η < 1/2) (hA : Entrance (C:=C) D Y r P t) (h : Y.sigma=(r:ℝ)+1-η)
    (hk : Ticket D Y r P) :
    ∀ᶠ m : ℕ in atTop,∀ N q, q∈D → m≤N → ∃ L,Obtains N q m Y r (P N q) (t N q) L := by
  have hv:= shopping (t:=t) hg ht hr he h hk (hA.budgets.mono fun i hi N p hp h => hi N p hp h.le |>.predicted)
  filter_upwards [tail hg ht hA,hv] with m H hw N q hD hN
  obtain ⟨L,hL⟩:= H N q hD hN
  exact ⟨L,⟨hw N q hD _ (fun i hm hi=>hL.costs i hi hm),hL⟩⟩
end YM.IterationFour.Vacuum
