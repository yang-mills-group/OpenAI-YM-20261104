import YM.Integration.SignedTreeTransport

/-! The separated two-scale tree OPE for interacting finite Wilson laws.
Its entire signed discrepancy is transported on the original history before
taking a mean. The inner cutoff and period and every legal comparison level
are retained. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedTreeWilson
open Function Filter Set MeasureTheory Spec OPE OPE.Orbits PhysMS Wilson Trace.Pilot
open FVA2 Pert.Position Maxwell Maxwell.Free MSbar.OPE RG11.Neighborhood
open OPETreeRemainder SignedTreeTransport
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (hS : Services C f S) (hV : ∀ d, Bid.pop (C.localSection d))
    {Q : MS.Land.Booked (FVA2.ColorCode.wings G)} (M : MS.Land.MS_Data G Q) (μ : ℝ)
    {n m i d : ℕ} (x : conf n) (y : Tail m) (v : Fin n → E C.labels i)
    (w : Fin m → E C.labels d) (weights : Fin n → ℕ) (H : ℕ)

/-- One interacting configuration supplies every factor in the full
input/exterior product and in each member of the finite output sum. -/
def grouped (r t : ℝ) (N p : ℕ) : Config G (C.side N p) → ℂ := fun U =>
  (t : ℂ)^(∑ a, weights a) * observable J r (driven t x.val y) v w N p U -
    ∑ k ∈ Finset.range (H+1), (t : ℂ)^k *
      observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p U

theorem grouped_continuous (r t : ℝ) (N p : ℕ) :
    Continuous (grouped J x y v w weights H r t N p) :=
  ((observable_continuous J r (driven t x.val y) v w N p).const_mul _).sub
    (continuous_finsetSum _ fun k _ =>
      (observable_continuous J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p).const_mul _)

theorem grouped_mean (r t : ℝ) (N p : ℕ) :
    moment (C.beta N p) (grouped J x y v w weights H r t N p) =
    (t : ℂ)^(∑ a, weights a) * moment (C.beta N p) (observable J r (driven t x.val y) v w N p) -
      ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * moment (C.beta N p)
        (observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p) := by
  let μ := law G (C.side N p) (C.beta N p)
  let b k := observable J r (close y) (fun _ : Fin 1 => output C.labels x v k) w N p
  have hb (k : ℕ) : Integrable (fun U => (t : ℂ)^k * b k U) μ :=
    (continuous_integrable _ (observable_continuous J r _ _ w N p)).const_mul _
  have ha := (continuous_integrable (C.beta N p)
    (observable_continuous J r (driven t x.val y) v w N p)).const_mul ((t : ℂ)^(∑ a,weights a))
  change (∫ U, _ - ∑ k ∈ Finset.range (H+1), (t : ℂ)^k * b k U ∂μ) = _
  rw [integral_sub ha (integrable_finsetSum _ fun k _ => hb k), integral_const_mul,
    integral_finsetSum _ fun k _ => hb k]
  simp_rw [integral_const_mul]
  rfl

include hS in
/-- With the scale and configuration fixed, full signed cancellation
survives removal of both of the original regulators. -/
theorem grouped_limit (r t : ℝ) (hr : 0 < r) (ht : driven t x.val y ∈ conf (n+m)) :
    Tendsto (fun a : ℕ × ℕ => moment (C.beta a.1 a.2) (grouped J x y v w weights H r t a.1 a.2))
      f.fuse (𝓝 (OPETreePhysical.discrepancy F J x y v w weights H none r t)) := by
  have h := ((observable_limit F hS J r hr _ ht v w).const_mul ((t : ℂ)^(∑ a, weights a))).sub
    (tendsto_finsetSum (Finset.range (H+1)) fun k _ =>
      (observable_limit F hS J r hr _ (OPEMSReport.close_conf y)
        (fun _ : Fin 1 => output C.labels x v k) w).const_mul ((t : ℂ)^k))
  exact h.congr' (Eventually.of_forall fun a => (grouped_mean J x y v w weights H r t a.1 a.2).symm)

variable (hv : ∀ a, pureW scaleW (weights a) (polynomials C.labels i v a))
include hJ hG X hR hS hV M μ hv

/-- The independent finite-part MS tree coefficient supplies the physical
output. The outer shape ratio and physical scale can be taken consecutively
with the complete original mesh/period schedule still inside both. -/
theorem two_scale :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse,
      ∀ (j : ℕ) (hj : j ≤ a.1), ‖mean C a.1 a.2 j hj
        (grouped J x y v w weights H r t a.1 a.2)‖ ≤ K*t^(H+1) := by
  obtain ⟨K,hK,h⟩ := OPETreePhysical.two_scale F R J hJ hG X hR F.room.cutoff hV M μ
    x y v w weights H hv
  refine ⟨K+1,by linarith,?_⟩
  filter_upwards [h, self_mem_nhdsWithin,
    (contracts (x := x.val) y.c y.y (exterior_apart y)).filter_mono nhdsWithin_le_nhds]
    with t ht hp hfar
  have htpos : 0 < t := hp
  have hsep : driven t x.val y ∈ conf (n+m) :=
    combination (safe x.property y.c htpos) (Points.tail_in y.apart) hfar
  filter_upwards [ht, self_mem_nhdsWithin] with r hr hrpos
  have hreg := Metric.tendsto_nhds.mp (grouped_limit F J hS x y v w weights H r t hrpos hsep)
    (t^(H+1)) (pow_pos htpos _)
  filter_upwards [hreg] with a ha j hj
  rw [mean_eq F.room.cutoff _ _ _ hj _ (grouped_continuous J x y v w weights H r t a.1 a.2)]
  rw [dist_eq_norm] at ha
  exact (norm_le_norm_sub_add _ _).trans
    ((add_le_add ha.le (hr none)).trans_eq (by ring))

/-- The full physical small-scale filter admits a single shrinking shape
ratio for which all nested finite regulator pairs and all intermediate
levels enjoy the same engineering power saving. -/
theorem simultaneous :
    ∃ K : ℝ, 0 < K ∧ ∃ ratio : ℝ → ℝ, Tendsto ratio trail (𝓝[>] 0) ∧
      ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse, ∀ (j : ℕ) (hj : j ≤ a.1),
        ‖mean C a.1 a.2 j hj (grouped J x y v w weights H r (ratio r) a.1 a.2)‖ ≤
          K*(ratio r)^(H+1) := by
  obtain ⟨K,hK,h⟩ := two_scale F R J hJ hG X hR hS hV M μ x y v w weights H hv
  let t := fun j : ℕ => 1 / ((j : ℝ)+1)
  have ht : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun j => by
      change 0 < 1 / ((j : ℝ)+1); positivity)⟩
  obtain ⟨a,ha,had⟩ := OPETreePhysical.slow_demand (fun j r => ∀ᶠ b : ℕ × ℕ in f.fuse,
    ∀ (l : ℕ) (hl : l ≤ b.1), ‖mean C b.1 b.2 l hl
      (grouped J x y v w weights H r (t j) b.1 b.2)‖ ≤ K*(t j)^(H+1)) (ht.eventually h)
  exact ⟨K,hK,t ∘ a,ht.comp ha,had⟩

end YM.Integration.SignedTreeWilson
