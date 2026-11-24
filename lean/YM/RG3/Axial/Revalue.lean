import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Recenter

/-!
# Small ordinary jets → real local price. I: Fréchet estimates

To compare on true fields, not just jets, we use the actual neighborhood
of the *raw*, all-link chart. The high order budget is on a specified real
ball (NOT differentiating through clipping or any mask). Its input price `c`
can come e.g. from constituent holonomies with true path charges or from
separately supplied estimates on raw link/noise computations AFTER holding
the queries. The low jet tests may instead exploit summed cancellations but
must be on the indicated chart and for the indicated WHOLE function.
Compatible with a producer giving tests in directions uniform in link norm,
via `Ordinary.at` and `ContinuousMultilinearMap.opNorm_le_bound`. Taylor
powers here are in the genuine small-link radius, not divided by g. Delay
that radius as usual when the order is moving! All constants for fixed order
explicit and period-free; don't use them unchanged for an unbounded-order
statement. The protocol here differs from `Trace.Physical.LogAccuracy`,
where *zero* low jets suffice in the presence of a complete bound on ALL
unmasked left derivatives: we impose only raw prices for higher orders and
keep the discrepancy on low jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Axial
open Function Lattice RG Wilson SelectedOrderedKernels Filter Metric WardBin.Lies
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {r k i : ℕ} {τ ε c : ℝ}

/-- For all z in a *closed* ball (or stronger estimates). No factorials
implicit in any ordinary price. `k` must cover the order of the price we
want OUT plus (i.e. also cover) the dividing horizon r. `ε` is a small-price
budget; it may be zero but isn't required to be. -/
structure Ordinary (f : W → E) (r k : ℕ) (τ ε c : ℝ) : Prop where
  tau : 0 ≤ τ
  below : τ ≤ 1
  small : 0 ≤ ε
  high : 0 ≤ c
  dividing : r ≤ k
  germ (z : W) : ‖z‖ ≤ τ → ContDiffAt ℝ k f z
  low i : i < r → ‖iteratedFDeriv ℝ i f 0‖ ≤ ε
  payment (z : W) (i : ℕ) : ‖z‖ ≤ τ → r ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f z‖ ≤ c

namespace Ordinary
variable {f : W → E} (h : Ordinary f r k τ ε c)
include h

/-- Elementary downhill bootstrapping without giving up powers in τ. -/
theorem near (z : W) (hz : ‖z‖ ≤ τ) (hi : i ≤ r) :
    ‖iteratedFDeriv ℝ i f z‖ ≤ c*τ^(r-i) + ((r-i:ℕ):ℝ)*ε := by
  induction hi using Nat.decreasingInduction generalizing z with
  | self => simpa using h.payment z r hz le_rfl h.dividing
  | of_succ i hi ih =>
    let m:=i+1; let N:=c*τ^(r-m)+((r-m:ℕ):ℝ)*ε
    have hh : (i:ℕ∞ω) < (k:ℕ∞ω) := by exact_mod_cast hi.trans_le h.dividing
    have he := h.low i hi
    let s:= Metric.closedBall (0:W) τ
    have hx (y : W) (hy : y∈s) : ‖y‖ ≤ τ := by simpa [s] using hy
    have smooth : ∀ y∈s,DifferentiableAt ℝ (iteratedFDeriv ℝ i f) y := fun y hy =>
      (h.germ y (hx y hy)).differentiableAt_iteratedFDeriv hh
    have bound (y : W) (hy : y∈s) : ‖fderiv ℝ (iteratedFDeriv ℝ i f) y‖ ≤ N := by
      rw [norm_fderiv_iteratedFDeriv]; exact ih y (hx y hy)
    have hv := (convex_closedBall (0:W) τ).norm_image_sub_le_of_norm_fderiv_le smooth bound
      (Metric.mem_closedBall_self h.tau) (Metric.mem_closedBall.mpr (by rwa [dist_zero_right] : dist z 0 ≤ τ))
    rw [sub_zero] at hv; have ht := h.tau; have ho:=h.high; have hsw:=h.small; have hs:=h.below
    have hN : 0≤N:= by unfold N; positivity
    have hm: r-i= r-m+1:=by unfold m; omega
    refine (norm_le_norm_sub_add _ (iteratedFDeriv ℝ i f 0)).trans ((add_le_add
      (hv.trans (mul_le_mul_of_nonneg_left hz hN)) he).trans ?_)
    rw [hm, Nat.cast_add, Nat.cast_one, pow_succ]
    unfold N
    have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ ((r-m:ℕ):ℝ)*ε by positivity)
    linarith only [hb]

/-- Price when each derivative leg, even at high order, receives one τ.
Ordinary divergence powers e.g. of an explicit g still have to be paid on
this whole price. -/
theorem cover (z : W) (hz : ‖z‖ ≤ τ) (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i f z‖ * τ^i ≤ c*τ^r + (r:ℝ)*ε := by
  have hs:=h.tau; have he:=h.below
  by_cases hp : r ≤ i
  · exact ((mul_le_mul (h.payment z i hz hp hi) (pow_le_pow_of_le_one hs he hp) (pow_nonneg hs _) h.high)).trans
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) h.small))
  have hb : i ≤ r := (not_le.mp hp).le
  refine ((mul_le_mul_of_nonneg_right (h.near z hz hb) (pow_nonneg hs _))).trans ?_
  rw [add_mul, mul_assoc c, ← pow_add,r.sub_add_cancel hb]
  apply add_le_add_right
  have h' := mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (show r-i ≤ r from Nat.sub_le _ _)) h.small
  exact (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) h.small) (pow_le_one₀ hs he)).trans h'

end Ordinary

/-- A partition's genuine chain-rule price. Counts every term, including
zero derivative with its single partition. We pay one τ per *block* outside,
which is enough since the derivative is of that block order. -/
def profit (G : Gauge) {j : ℕ} (p : OrderedFinpartition j) := ∏ b, charge G j (p.partSize b)
lemma profit_nn (G : Gauge) {j : ℕ} (p : OrderedFinpartition j) : 0 ≤ profit G p := Finset.prod_nonneg fun _ _ => charge_nn ..

def fees (G : Gauge) (k : ℕ) : ℝ := ∑ j∈Finset.range (k+1), ∑ p : OrderedFinpartition j, profit G p
lemma fees_nn (G : Gauge) (k : ℕ) : 0 ≤ fees G k := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => profit_nn ..
lemma fees_le (G : Gauge) {k j : ℕ} (h : j ≤ k) : ∑ p : OrderedFinpartition j, profit G p ≤ fees G k :=
  Finset.single_le_sum (f:=fun j => ∑ p : OrderedFinpartition j, profit G p) (fun _ _ => Finset.sum_nonneg (fun _ _ => profit_nn ..)) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

def balance (G : Gauge) (k r : ℕ) (τ ε c : ℝ) : ℝ := fees G k * (c*τ^r+r*ε)
lemma balance_nn (G : Gauge) (k r : ℕ) (hτ : 0 ≤ τ) (he : 0 ≤ ε) (hc : 0 ≤ c) : 0 ≤ balance G k r τ ε c := mul_nonneg (fees_nn ..) (by positivity)

variable {G : Gauge} {n : Side} {F : Config G n → E}
  (hF : Ordinary (F ∘ increment 1) r k τ ε c) {U : Directions G n}
  (hu : ‖U‖ ≤ τ) (hR : ∀ x, ‖U x‖ < radius G k)
include hF hu hR

/-- Transport for true LEFT jets on the displacement `U`. Input is in
real logarithmic variables; no factorial weights. Every explicit derivative
must be uniformly small linkwise (apply this AFTER paying the test weights
and using locality). Expansion preserves order only allowing chain-rule
terms of all lower ordinary orders, with one real small factor per block
(without needing to identify the exact partition products). -/
theorem stationed {j : ℕ} (A : Slab G n j) (ha : ∀ i, ‖A i‖ ≤ τ) (hj : j ≤ k) :
    ‖leftDerivs F (List.ofFn A) (increment 1 U)‖ ≤ balance G k r τ ε c := by
  let f:=F ∘ increment (1:Config G n)
  have hsm : ContDiffAt ℝ j f (through (siteFrame U j) 0) := (initial hR j).symm ▸
    (hF.germ U hu).of_le (Nat.cast_le.mpr hj)
  have hv : j ≤ k+1:= hj.trans (Nat.le_succ k)
  rw [expand_local (F:=F) (f:=f) (siteFrame U j)
    (fun e => (reframe hR hv e).of_le le_top) hsm ((ordered_chug hR hv _).fun_comp F) A,initial hR]
  let Z : ℝ := c*τ^r+r*ε; have hc := hF.high; have he := hF.small; have ht := hF.tau
  have hZ : 0 ≤ Z:=by unfold Z; positivity
  have hp (p : OrderedFinpartition j) :
      ‖iteratedFDeriv ℝ p.length f U (term (siteFrame U j) p A)‖ ≤ profit G p * Z:= by
    have h a (e : Edge (Site n)) :
        ‖term (siteFrame U j) p A a e‖ ≤ charge G j (p.partSize a) * τ := by
      have hz := reframe_cost hR hv (p.partSize_le a) e
      refine (term_cost _ _ _ _ _).trans ((mul_le_mul hz ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (charge_nn ..)))
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (norm_le_pi_norm _ _).trans (ha _))).trans ?_
      simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin];
      conv_rhs => rw [← pow_one τ]
      exact pow_le_pow_of_le_one ht hF.below (p.partSize_pos a)
    refine ((iteratedFDeriv ℝ p.length f U).le_opNorm _).trans ?_
    let T:=iteratedFDeriv ℝ p.length f U
    refine (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=> norm_nonneg _)
      (fun b _=> (pi_norm_le_iff_of_nonneg (mul_nonneg (charge_nn ..) ht)).mpr (h b))) (norm_nonneg T)).trans ?_
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin, show (∏ b,charge G j (p.partSize b))= profit G p from rfl]
    rw [mul_left_comm,← mul_assoc, mul_assoc (profit G p)]
    exact mul_le_mul_of_nonneg_left (hF.cover U hu (p.length_le.trans hj)) (profit_nn ..)
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (fun p _=> hp p)).trans ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (fees_le G hj) hZ
end YM.RG3.Axial
