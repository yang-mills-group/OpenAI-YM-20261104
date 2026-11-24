import YM.FormalOPE.RG10.Transit.Crumbs

/-!
# Rule for first-join and terminal costs before an arbitrary finer-tail endpoint

First-join and terminal bounds use compatible geometric slab and moment data (output root gauge may
be chosen relative to the entire family of supports). Need only singleton/root/profile and stable
invariant-transfer commitments. Coefficient bounds include log-reset structure via Hours. Future
uses require instantiating real physical Wilson windows and parameters; analytic hypotheses are
in *formal* norms only here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit.Weave
open Route PowerSeries Finset Function Voyage
open scoped Topology BigOperators Classical
variable {U J : ℕ→Type} {X : Type} {I : Type*} [DecidableEq I]
    [∀ i,Fintype (J i)] [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)]
    (V : Voyage U J) (W : Scale X U)
    (F : ∀ i, Subring (Channel (U i)))
variable (k N : ℕ) (v : Finset I) (P : I → Channel (U N)) (R C : ℝ)
    (r d n : ℕ) (D t H : I → ℕ) (δ : ℕ)
variable (O : Lens W.tape) (A : I → Lens W.tape)

def maximumNeeded (n r d : ℕ) := max n (Episode.momentIn r d n)
def tally (W : Scale X U) (C R : ℝ) (j t d : ℕ) := W.Y C R j^t * (R/W.μ j)^d

/-- Before selecting any parent/root. Hypotheses about one-mark stencils fully tested (own
horizon assigned by H; geometry in Lens, no moment bound on join expressions here). Use even
for growing schedules when those supplying hypotheses at each k are uniform. Cost estimates all
assume *only* THIS window and these orders/derivatives, constant choices independent of outside
finer/older tails. -/
structure Contracts (V : Voyage U J) (W : Scale X U) (F : ∀ i, Subring (Channel (U i)))
    (k N : ℕ) (r d n : ℕ) (R C : ℝ) (δ : ℕ) (v : Finset I) (P : I→Channel (U N))
    (O : Lens W.tape) (A : I→ Lens W.tape) (D t H : I→ℕ) : Prop extends Regular V W R C δ k N r d n F O where
  card : (v.card:ℝ) ≤ C
  rankMark i (h : i∈v) : Guard (P i) r (D i)
  invariantMark i (h : i∈v) : P i∈ F N
  totalrank : ∑ i∈v,D i ≤ d
  near i (h : i∈v) : O.m ≤ (A i).m
  -- actual physical-unit test clearance or larger. q finite powers; etc.
  gap i (h : i∈v) j (h' : j∈v) (hn : i≠j) : (A i).Spaced (A j) (R/C^δ)
  oneMark i (h : i∈v) j (hj : j ∈ Icc k N) : W.value j (maximumNeeded n r d) r (A i) (letter V P j i) ≤ tally W C R j (t i) (H i)

variable {V W F k N r d n R C δ v P O A D t H}
    (h : Contracts V W F k N r d n R C δ v P O A D t H) {i j : ℕ}
local notation "Y" => W.Y C R
local notation "μ" => W.μ
local notation "τ" => ∑ i∈v,t i
local notation "η" => ∑ i∈v,H i
local notation "L" => R/C^δ
local notation "Fh" => W.value j n r O
local notation "p" => Episode.pressure r d
include h in
omit [DecidableEq I] in
lemma Contracts.comm : Sane V k N F v P r D := ⟨h.selfish,h.toRegular.rank,h.invariantMark,h.rankMark⟩

omit [DecidableEq I] [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] in
lemma tallying : (∏ i∈v,tally W C R j (t i) (H i)) = tally W C R j τ η := by
  unfold tally; rw [prod_mul_distrib,prod_pow_eq_pow_sum,prod_pow_eq_pow_sum]
include h
omit [DecidableEq I] in
lemma separately (hj:j∈ Icc k N) : Fh (solo V v P j) ≤ tally W C R j τ η := by
  rw [← tallying (t:=t) (H:=H)]; apply (mag_prod (W.eyes j O) n r (W.alive _ _) v _).trans; refine prod_le_prod (fun i _=> W.nn ..) (fun i hi=>?_);
  apply ((W.mono ..).trans ((W.sooner j (A i) n r _ _ (le_max_left ..)).trans (h.oneMark i hi j hj))) -- inspect
  exact h.near i hi

def transitOne (r d n δ tt ee : ℕ) := 1+δ*Episode.pressure r d+δ*tt+δ*ee+n*δ
local notation "Y₁" => transitOne r d n δ τ η

lemma bill_item (hr : η ≤ n) (hj:j∈Ico k N) : Fh (expense V v P j) ≤ Y j^Y₁*(μ j/R)^(n-η) := by
  let WQ (i:I):=tally W C R (j+1) (t i) (H i)
  have he := Ico_subset_Icc_self hj -- name
  have hc := h.toRegular.toHours
  have hy : j+1∈Icc k N:= mem_Icc.mpr ⟨(mem_Ico.mp hj).1.trans (Nat.le_succ _),(mem_Ico.mp hj).2⟩
  have hY := hc.paid (mem_Ico.mp hj).1
  have hA : 0 ≤ C:= by linarith [hc.rich]
  have hR:=hc.R_pos; have hm:=W.positive j; have hX:=W.positive (j+1)
  have ht : tip (L/μ j) n * Fh (expense V v P j) ≤ v.card*((Y j^δ)^p * (∏ i∈v,WQ i)) := by
    apply Flock.priced V W j v (letter V P (j+1)) A O v _ _ d D WQ (h.fund _ hj) (h.comm.born hy) h.totalrank
      (by positivity) h.near h.gap (fun i hi=> (W.sooner (j+1) (A i) _ r _ _ (le_max_right ..)).trans (h.oneMark i hi (j+1) hy)) _ (Subset.refl _)
    intro i hi; rw [singling V P (mem_Ico.mp hj).2]; apply ((W.sooner j (A i) n r _ _ (le_max_left ..)).trans (h.oneMark i hi j he)).trans
    exact hc.earlier (mem_Ico.mp hj).1 (Nat.le_succ j)
  unfold transitOne; rw [Nat.mul_comm n]
  apply hc.reap (mem_Ico.mp hj).1 _ _ _ hr (le_trans ht ?_)
  unfold WQ; rw [tallying]
  apply le_trans (mul_le_mul (h.card.trans (hc.zees (mem_Ico.mp hj).1)) (mul_le_mul_of_nonneg_left (hc.further j η hj τ) (by positivity)) ?_ hY) ?_ -- reorder
  · have hw : 0≤Y (j+1):= hc.paid (mem_Icc.mp hy).1; positivity
  simp only [pow_add,pow_mul]; exact Eq.le (by ring)

-- cost after controlling the tail

def debited (r d n δ tt ee : ℕ) := Scale.absorb (δ+transitOne r d n δ tt ee)
local notation "N₀" => debited r d n δ τ η

theorem aperture (hn : η+2 ≤ n) (hj:j∈ Icc k N) :
    Fh (all V v P j-solo V v P j) ≤ Y j^N₀ * (μ j/R)^(n-η) := by
  obtain ⟨hx,hh⟩:=mem_Icc.mp hj
  rw [founded V v P hh, add_sub_cancel_left]; apply (W.sum' ..).trans
  apply le_trans _ (W.shorten R C h.base h.rich (n-η) (δ+Y₁) (by omega) hx hh)
  refine sum_le_sum fun i hi=>?_;
  have hr := Ico_subset_Icc_self hi; have h' := Ico_subset_Ico hx le_rfl hi; have H:=h.toRegular.toHours.paid ((mem_Ico.mp h').1)
  rw [pow_add,mul_assoc];
  apply (h.stable _ hj _ hr _ (h.comm.remainder h') (Guard.mono (h.comm.record h') h.totalrank)).trans
  apply mul_le_mul_of_nonneg_left (bill_item h (by omega) h') (by positivity)

-- result incl arbitrary higher moments

theorem propagates (hn : η+2 ≤ n) (hj:j∈ Icc k N) :
    Fh (all V v P j) ≤ Y j^(max τ N₀+1)*(R/μ j)^η := by
  let t0:=Y j; let WQ:= max τ N₀
  have H:=h.toRegular.toHours; have ht : 2 ≤ t0 := H.richAt (mem_Icc.mp hj).1
  have hm:= W.positive j; have hR:=H.R_pos
  have hy := H.near1 (mem_Icc.mp hj).1
  let B := (R/μ j)^η; have hB : 1 ≤ B := one_le_pow₀ hy
  have ha : (μ j/R)^(n-η) ≤ B := (pow_le_one₀ (by positivity) ((div_le_one hR).mpr ((one_le_div hm).mp hy))).trans hB
  have hv : 0<t0:=by linarith
  let K:=t0^WQ * B
  have hh : 0 ≤ K := mul_nonneg (pow_nonneg hv.le _) (zero_le_one.trans hB)
  nth_rw 1 [← sub_add_cancel (all V v P j) (solo V v P j)]
  apply (W.add ..).trans; apply le_trans (b:=K+K) (add_le_add ?_ ?_) ?_;
  · apply (aperture h hn hj).trans; exact mul_le_mul (pow_le_pow_right₀ (by linarith) (le_max_right ..)) ha (by positivity) (by positivity)
  · apply (separately h hj).trans; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (le_max_left ..)) (zero_le_one.trans hB)
  change K+K ≤ t0^(WQ+1)*B; calc
    _ = 2*K := by ring
    _ ≤ t0*K := mul_le_mul_of_nonneg_right ht hh
    _ = _ := by unfold K; rw [pow_succ]; ring
end YM.FormalOPE.RG10.Transit.Weave
