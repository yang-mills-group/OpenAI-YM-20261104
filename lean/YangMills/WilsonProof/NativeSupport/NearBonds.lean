import YangMills.WilsonProof.NativeSupport.FrozenPicture

/-! Pointwise and spatial-neighborhood estimates for the exact normalized
inlet picture. All measurements use one joint path, including its tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice RG Wilson Tree RGComparison.Core16 YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedCovariance
open WilsonUniformUnmarkedInletBondCovariances WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators Topology

variable {G : Gauge} {n c : Side}

private lemma unit_nonneg (d : Descent n c) (Y : ℕ → ℝ) (t : d.Tags)
    (V : Config G c) (x : Descent.Fields G d) : 0 ≤ d.integrand Y t 1 V x := by
  change 0 ≤ d.probability t x * Real.exp _ * 1
  exact mul_nonneg (mul_nonneg (d.probability_nonneg ..) (Real.exp_pos _).le) zero_le_one

private lemma normalized_bound (d : Descent n c) (h : d.OK G) (Y : ℕ → ℝ) (V : Config G c)
    (f : d.Tags → Descent.Fields G d → ℝ) (C : ℝ)
    (bound : ∀ t x, |f t x| ≤ C * d.integrand Y t 1 V x) :
    |(∑ t, ∫ x, f t x ∂d.measure G) / mass d Y 1 V| ≤ C := by
  have hm := positive d h Y V
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc
    _ ≤ ∑ t, |∫ x, f t x ∂d.measure G| := Finset.abs_sum_le_sum_abs .. 
    _ ≤ ∑ t, ∫ x, C * d.integrand Y t 1 V x ∂d.measure G := by
      apply sum_le_sum
      intro t _
      exact norm_integral_le_of_norm_le (f := f t) ((d.path_integrable h Y t 1 continuous_const V).const_mul C)
        (ae_of_all _ (bound t))
    _ = _ := by simp_rw [integral_const_mul]; rw [mass, mul_sum]

private lemma weight_mul (d : Descent n c) (Y : ℕ → ℝ) (t : d.Tags) (V : Config G c)
    (f : Config G n → ℝ) (x : Descent.Fields G d) :
    d.integrand Y t f V x = d.integrand Y t 1 V x * f (d.fine V x) := by
  simp [Descent.integrand]

theorem one_bond (d : Descent n c) (h : d.OK G) (β v : ℕ → ℝ) (V : Config G c)
    {φ : Config G n → ℝ} (test : Continuous φ) (symm : GaugeInvariant φ)
    {S : ℝ} (bill : ∀ U, |φ U| ≤ S) (r : ℝ) (q : sites n d) :
    |picture d β v V φ r q| ≤ cap d q * (2 * S) := by
  let Y := WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
  have mean : |d.conditioned Y φ V| ≤ S := by
    rw [fraction d h Y V test symm]
    apply normalized_bound d h Y V
    intro t x
    rw [weight_mul d Y t V φ x, abs_mul, abs_of_nonneg (unit_nonneg ..), mul_comm]
    exact mul_le_mul_of_nonneg_right (bill _) (unit_nonneg ..)
  apply normalized_bound d h Y V
  intro t x
  have he := bounded d t V x q
  have hc : |φ (d.fine V x) - d.conditioned Y φ V| ≤ 2 * S :=
    (abs_sub _ _).trans (by linarith only [bill (d.fine V x), mean])
  rw [weight_mul d Y t V, abs_mul, abs_neg, abs_of_nonneg he.1, abs_mul,
    abs_of_nonneg (unit_nonneg ..)]
  calc
    _ = (cell G d t V x q * |φ (d.fine V x) - d.conditioned Y φ V|) * d.integrand Y t 1 V x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul he.2 hc (abs_nonneg _) (he.1.trans he.2)) (unit_nonneg ..)

/-- Native homes of a fine source, with the same ratios as the traversal. -/
def home {n : Side} : {c : Side} → Descent n c → Site n → Site c
  | _, .nil => id
  | _, .push S _ d => S.ratio.parent ∘ home d

/-- All four orientations based at integer offsets in the indicated native box.
Taking an image makes the definition work unchanged on very small periods. -/
def boxes {c : Side} {m : ℕ} (o : Fin m → Site c) (R : ℕ) : Finset (Bond c) :=
  univ.image fun z : Fin m × (Axis → Fin (2*R+1)) × Axis =>
    (o z.1 + wrap c (fun i => (z.2.1 i : ℤ) - R), z.2.2)

lemma card_boxes {c : Side} {m : ℕ} (o : Fin m → Site c) (R : ℕ) :
    (boxes o R).card ≤ m * ((2*R+1)^4 * 4) := by
  refine card_image_le.trans ?_
  simp [Axis]

def window {n : Side} {m : ℕ} (o : Fin m → Site n) (R : ℕ) :
    {c : Side} → (d : Descent n c) → Finset (sites n d)
  | _, .nil => ∅
  | _, .push S T d => (boxes (home (.push S T d) ∘ o) R).disjSum (window o R d)

lemma card_window {m : ℕ} (o : Fin m → Site n) (R : ℕ) (d : Descent n c) :
    (window o R d).card ≤ d.depth * (m * ((2*R+1)^4 * 4)) := by
  induction d with
  | nil => simp [window, Descent.depth]
  | @push c f S T d ih =>
    change ((boxes (home (.push S T d) ∘ o) R).disjSum _).card ≤ (d.depth+1)*_
    rw [card_disjSum, add_mul, one_mul, add_comm (d.depth*_)]
    exact Nat.add_le_add (card_boxes ..) ih

/-- Directly usable with the actual common per-link cap of a physical run.
The region may contain several arbitrarily separated groups of placements. -/
theorem near_bonds (d : Descent n c) (h : d.OK G) (β v : ℕ → ℝ) (V : Config G c)
    {φ : Config G n → ℝ} (test : Continuous φ) (symm : GaugeInvariant φ)
    {S E : ℝ} (bill : ∀ U, |φ U| ≤ S) (hE : 0 ≤ E)
    (link_cap : ∀ q ∈ interior d, cap d q ≤ E) (r : ℝ)
    {m : ℕ} (o : Fin m → Site n) (R : ℕ) :
    ∑ q ∈ window o R d ∩ interior d, |picture d β v V φ r q| ≤
      (d.depth * (m * ((2*R+1)^4 * 4)) : ℕ) * (E * (2*S)) := by
  let W := window o R d ∩ interior d
  have hS : 0 ≤ S := (abs_nonneg _).trans (bill 1)
  have card : W.card ≤ d.depth * (m * ((2*R+1)^4*4)) :=
    (card_le_card inter_subset_left).trans (card_window o R d)
  calc
    _ ≤ ∑ _q ∈ W, E*(2*S) := sum_le_sum fun q hq =>
      (one_bond d h β v V test symm bill r q).trans
        (mul_le_mul_of_nonneg_right (link_cap q (mem_inter.mp hq).2) (by positivity))
    _ = (W.card : ℝ) * (E * (2*S)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card) (by positivity)

/-- The weaker signed-layer bill is literally sufficient for the weighted sum
in the mean-value identity; no interchange of laws or mean-value points. -/
theorem layer_bill (d : Descent n c) (v : ℕ → ℝ) (F : sites n d → ℝ)
    {η : ℝ} (price : ∀ j, 0 < j → j < d.depth → |v j| ≤ η) :
    |∑ q ∈ interior d, v (lag d q)*F q| ≤
      η * ∑ j ∈ Ioo 0 d.depth, |∑ q ∈ (interior d).filter (fun q => lag d q = j), F q| := by
  have dates' : ∀ q ∈ interior d, lag d q ∈ Ioo 0 d.depth := fun _ h =>
    mem_Ioo.mpr (mem_filter.mp h).2
  rw [← sum_fiberwise_of_maps_to dates' (fun q => v (lag d q)*F q)]
  have single (j : ℕ) : ∑ q ∈ (interior d).filter (fun q => lag d q = j), v (lag d q)*F q =
      v j * ∑ q ∈ (interior d).filter (fun q => lag d q = j), F q := by
    rw [mul_sum]
    exact sum_congr rfl fun q hq => by rw [(mem_filter.mp hq).2]
  simp_rw [single]
  exact (Finset.abs_sum_le_sum_abs ..).trans (by
    rw [mul_sum]
    exact sum_le_sum fun j hj => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (price j (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2) (abs_nonneg _))

theorem signed_shift (d : Descent n c) (h : d.OK G) (β v : ℕ → ℝ)
    (endpoint : v d.depth = 0) (V : Config G c) {φ : Config G n → ℝ}
    (test : Continuous φ) (symm : GaugeInvariant φ)
    {η : ℝ} (price : ∀ j, 0 < j → j < d.depth → |v j| ≤ η) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      |d.conditioned (β+v) φ V - d.conditioned β φ V| ≤
        η * ∑ j ∈ Ioo 0 d.depth,
          |∑ q ∈ (interior d).filter (fun q => lag d q = j), picture d β v V φ r q| := by
  obtain ⟨r, hr, eq⟩ := WilsonUniformUnmarkedInletConnectedShift.shift d h β v V test symm
  refine ⟨r, hr, ?_⟩
  rw [eq, WilsonUniformUnmarkedInletBondCovariances.centered d h β v endpoint V test r]
  exact layer_bill d v (picture d β v V φ r) price

end YM.Integration.InletSusceptibility
