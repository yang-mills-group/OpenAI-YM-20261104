import YM.Integration.WilsonPositionSeparatedProfileMatching

/-! The finite Wilson position prescription on a single auxiliary mesh,
with a compact test price independent of the truncation variable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionFiniteMSBank

open Filter Function Finset Set
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb RG17 Trace.Pilot PhysMS PhysicalNext.Repeat.Legato
open WilsonPositionSeparatedProfileMatching
open scoped Topology BigOperators Classical

variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)

def finite (m : XSpace.Mesh) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) (t : ℝ) : ℂ :=
  ∑ k : Fin (q+1), (t : ℂ)^k.val * Scale.System.positions Z.scheme Z.criterion d m k n φ v

include H in
private theorem readout (ν : ℝ) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (j : ℕ) :
    Scale.System.Readout Z.scheme Z.criterion T ν d j n φ v = coefficient Z T ν d φ v j := by
  rw [H.transformedTest ν d n j φ v]
  apply φ.apply_eq
  intro x hx
  simp only [Jury.fxt, extended, dif_pos hx, WilsonPositionHomogeneousComparison.coefficient]

include H in
theorem limit (ν : ℝ) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) (t : ℝ) :
    Tendsto (fun i => finite Z (Z.run.step i) d φ v q t) atTop (𝓝 (polynomial Z T ν d φ v q t)) := by
  unfold polynomial
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (t : ℂ)^j * coefficient Z T ν d φ v j) (q+1)]
  exact tendsto_finsetSum univ fun j _ => tendsto_const_nhds.mul
    (by rw [← readout Z H ν d φ v j.val]; exact H.wilsonLimit ν n d j v φ)

include H in
theorem compact (ν : ℝ) (d n : ℕ) (v : Tags G d n) (q : ℕ) {K : Set (Points n)}
    (closed : IsCompact K) (clear : K ⊆ conf n) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ m : XSpace.Mesh in Front,
      ∀ (φ : Test n), tsupport φ ⊆ K → ∀ b, TestBudget.Bound φ b →
      ∀ t : ℝ, |t| ≤ 1 →
      ‖finite Z m d φ v q t - polynomial Z T ν d φ v q t‖ ≤ b*A*m.spacing^MS.Tide.mildG := by
  choose C positive budget using fun j : Fin (q+1) => H.uniformTest ν n d j v K closed clear
  have pos : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (positive j).le
  refine ⟨1 + ∑ j, C j, by linarith, ?_⟩
  filter_upwards [eventually_all.mpr budget] with m prices φ support b paid t unit
  have bp := (norm_nonneg (φ 0)).trans (paid 0).1
  have gain := Real.rpow_nonneg m.positive.le MS.Tide.mildG
  unfold finite polynomial
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (t : ℂ)^j * coefficient Z T ν d φ v j) (q+1),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin (q+1), b*C j*m.spacing^MS.Tide.mildG := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [←mul_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ←readout Z H ν d φ v j]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg t) unit) (norm_nonneg _)).trans
        (by simpa only [one_mul] using prices j φ support b paid)
    _ = b*(∑ j, C j)*m.spacing^MS.Tide.mildG := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ b*(1+∑ j,C j)*m.spacing^MS.Tide.mildG :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) bp) gain

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ → tower S)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

/-- The unselected physical reading at each fixed radius compared to the
truncated finite Wilson program at arbitrarily late auxiliary meshes. -/
def cofinal (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∃ᶠ i : ℕ in atTop,
    ‖observed Z F J none d φ v r - finite Z (Z.run.step i) d φ v q (θ r)‖ ≤ ε*|θ r|^q

include H in
theorem measured (ν : ℝ) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    {Y : (Bel R.family.book).Hierarchy} (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (X : Scaling S) (foundation : Foundation F reader) (realRate : Coupling G θ)
    (priced : cofinal Z F J d φ v q) : matchesThrough Z T F J ν d φ v q := by
  intro ε he
  have phase := phases Z F J reader lead paid hG X foundation d φ v θ realRate (half_pos he) q
  filter_upwards [priced (ε/2) (half_pos he), phase, realRate.positive] with r frequent dispersed gt p
  have lim := ((tendsto_const_nhds (x:=observed Z F J none d φ v r)).sub
    (limit Z H ν d φ v q (θ r))).norm
  have phys : ‖observed Z F J none d φ v r - polynomial Z T ν d φ v q (θ r)‖ ≤ (ε/2)*|θ r|^q := by
    by_contra! larger
    have strict := (tendsto_order.mp lim).1 _ larger
    obtain ⟨i,small,big⟩ := (frequent.and_eventually strict).exists
    exact (not_lt_of_ge small) big
  apply (norm_sub_le_norm_sub_add_norm_sub _ (observed Z F J none d φ v r) _).trans
  rw [abs_of_pos gt] at phys ⊢
  simpa only [←add_mul, add_halves] using add_le_add (dispersed p) phys

end YM.Integration.WilsonPositionFiniteMSBank
