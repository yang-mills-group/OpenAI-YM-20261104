import YM.MS.Dial.Watch
/-!
# Auxiliary estimates for quantitative continuity of the actual Dial kernels

Exponential notation for Hölder estimates (think of a pair of distance at
most `exp (-r)`). All costs here are joint in time, momentum chart inputs and
external positions. Use whole charts: a bound on each ray doesn't readily
pass through the loop integrations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real Finset
variable {E X J : Type} {Y : Type}
variable {T : X → X → ℝ → Prop} {B : ℝ → E → ℝ} {W : E → ℝ}

abbrev Profile (X E : Type) :=
  X → ℝ → E → ℂ
variable {F H : Profile X E}

/-- Basic individual estimate -/
def Funds (B : ℝ → E → ℝ) (W : E → ℝ) (F : Profile X E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x t p, ‖F x t p‖ ≤ C * B t p ^ n * W p

/-- Difference estimate for `T x y r` comparing x,y with precision `r` -/
def Holds (T : X → X → ℝ → Prop) (B : ℝ → E → ℝ) (W : E → ℝ) (F : Profile X E) : Prop :=
  ∃ a : ℝ,
    0 < a ∧
      ∃ C : ℝ,
        0 ≤ C ∧
          ∃ n : ℕ,
            ∀ x y (r : ℝ),
              0 ≤ r → T x y r → ∀ t p, ‖F x t p - F y t p‖ ≤ C * exp (-a * r) * B t p ^ n * W p

abbrev Handles T B W (F : Profile X E) :=
  Funds B W F ∧ Holds T B W F

lemma holding (f : ℝ → E → ℂ) : Holds T B W (fun _ => f) := by
  refine ⟨1, zero_lt_one, 0, le_rfl, 0, ?_⟩
  intro x y r hr H t p
  simp

lemma hold0 : Holds T B W (0 : Profile X E) :=
  holding _

lemma handles0 (T : X → X → ℝ → Prop) (B : ℝ → E → ℝ) (W : E → ℝ) : Handles T B W (0 : Profile X E) :=
  ⟨⟨0, le_rfl, 0, by simp⟩, hold0⟩

lemma Holds.add (hF : Holds T B W F) (hH : Holds T B W H) (hB : ∀ t p, 1 ≤ B t p)
    (hp : ∀ p, 0 ≤ W p) : Holds T B W (F + H) := by
  obtain ⟨a, ha, C, hC, n, h⟩ := hF
  obtain ⟨b, hb, D, hD, m, h'⟩ := hH
  let s := min a b
  refine ⟨s, lt_min ha hb, C + D, by positivity, n + m, ?_⟩
  intro x y r hr hT t p
  simp only [Pi.add_apply]
  rw [add_sub_add_comm]
  refine (norm_add_le ..).trans ((add_le_add (h _ _ _ hr hT t p) (h' _ _ _ hr hT t p)).trans ?_)
  rw [add_mul (C : ℝ) D, add_mul, add_mul]
  have hz := hp p
  apply add_le_add
  · gcongr
    · exact pow_nonneg (zero_le_one.trans (hB t p)) _
    · exact min_le_left ..
    · exact hB t p
    omega
  gcongr
  · exact pow_nonneg (zero_le_one.trans (hB t p)) _
  · exact min_le_right ..
  · exact hB t p
  omega

lemma Funds.add (hF : Funds B W F) (hh : Funds B W H) (hB : ∀ t p, 1 ≤ B t p) (hp : ∀ p, 0 ≤ W p) :
    Funds B W (F + H) := by
  obtain ⟨C, hC, n, h⟩ := hF
  obtain ⟨D, hD, m, h'⟩ := hh
  refine ⟨C + D, by positivity, n + m, ?_⟩
  intro x t p
  refine (norm_add_le ..).trans ((add_le_add (h x t p) (h' x t p)).trans ?_)
  have hz := hp p
  rw [add_mul, add_mul]
  exact
    add_le_add
      (by
        gcongr
        exact hB t p
        omega)
      (by
        gcongr
        exact hB t p
        omega)

lemma Handles.p_sum (U : Finset J) {f : J → Profile X E} (hf : ∀ i ∈ U, Handles T B W (f i))
    (hB : ∀ t p, 1 ≤ B t p) (hp : ∀ p, 0 ≤ W p) : Handles T B W (∑ i ∈ U, f i) := by
  classical
    induction U using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact handles0 ..
  | insert i U hi ih =>
    have hv := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have he := hf i (by simp)
    rw [Finset.sum_insert hi]
    exact ⟨he.1.add hv.1 hB hp, he.2.add hv.2 hB hp⟩

lemma Holds.p_sum (U : Finset J) {f : J → Profile X E} (hf : ∀ i ∈ U, Holds T B W (f i))
    (hB : ∀ t p, 1 ≤ B t p) (hp : ∀ p, 0 ≤ W p) : Holds T B W (∑ i ∈ U, f i) := by
  classical
    induction U using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact hold0
  | insert i U hi ih =>
    have hv := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have he := hf i (by simp)
    rw [Finset.sum_insert hi]
    exact he.add hv hB hp

lemma Handles.lsum (U : Finset J) {f : J → Profile X E} (hf : ∀ i ∈ U, Handles T B W (f i))
    (hB : ∀ t p, 1 ≤ B t p) (hp : ∀ p, 0 ≤ W p) : Handles T B W (fun x t p => ∑ i ∈ U, f i x t p) := by
  rw [show (fun x t p => ∑ i ∈ U, f i x t p) = ∑ i ∈ U, f i from
      funext fun _ => funext fun _ => funext fun _ => by simp [Finset.sum_apply]]
  exact Handles.p_sum U hf hB hp

lemma Handles.point (c : ℂ) : Handles T B 1 (fun _ _ _ => c) := by
  refine ⟨⟨‖c‖, norm_nonneg _, 0, fun x t p => ?_⟩, holding _⟩
  simp

section regular
variable [NormedAddCommGroup E]

def heft (p : E) :=
  1 + ‖p‖

def rope (t : ℝ) (p : E) :=
  exp |t| * heft p

lemma hefty (p : E) : 1 ≤ heft p := by simp [heft]

lemma hefty0 (p : E) : 0 < heft p :=
  lt_of_lt_of_le zero_lt_one (hefty p)

lemma ropey (t : ℝ) (p : E) : 1 ≤ rope t p :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_exp (abs_nonneg _)) (hefty _)

lemma ropey0 (t : ℝ) (p : E) : 0 < rope t p :=
  lt_of_lt_of_le zero_lt_one (ropey t p)

lemma rope_exp (t : ℝ) (p : E) (n : ℕ) : rope t p ^ n = exp (n * |t|) * heft p ^ n := by
  rw [rope, mul_pow, Real.exp_nat_mul]

abbrev Vouch (F : Profile X E) :=
  Funds rope 1 F

abbrev Sticky (T : X → X → ℝ → Prop) (F : Profile X E) :=
  Holds T rope 1 F

abbrev Tames (T : X → X → ℝ → Prop) (F : Profile X E) :=
  Handles T rope 1 F

lemma Holds.main_mul (h : Tames T F) (h' : Tames T H) : Sticky T (F * H) := by
  obtain ⟨⟨C, hC, n, h⟩, a, ha, D, hD, m, d⟩ := h
  obtain ⟨⟨C', hC', n', h'⟩, b, hb, D', hD', m', d'⟩ := h'
  let s := min a b
  refine ⟨s, lt_min ha hb, D * C' + C * D', by positivity, m + n' + (n + m'), ?_⟩
  intro x y r hr hT t p
  have ht := ropey0 t p
  simp only [Pi.mul_apply, Pi.one_apply, mul_one] at *
  rw [show
      F x t p * H x t p - F y t p * H y t p =
        (F x t p - F y t p) * H x t p + F y t p * (H x t p - H y t p)
      from (by ring)]
  apply (norm_add_le ..).trans
  rw [norm_mul, norm_mul]
  apply
    (add_le_add (mul_le_mul (d _ _ _ hr hT t p) (h' _ _ _) (norm_nonneg _) (by positivity))
        (mul_le_mul (h y t p) (d' _ _ _ hr hT t p) (norm_nonneg _) (by positivity))).trans
  rw [show _ * _ * (C' * _) = D * C' * exp (-a * r) * rope t p ^ (m + n') from
      (by
        rw [pow_add]
        ring),
    show _ * _ * (D' * _ * _) = C * D' * exp (-b * r) * rope t p ^ (n + m') from
      (by
        rw [pow_add]
        ring)]
  rw [add_mul (D * C') (C * D'), add_mul]
  have hmul (z : ℕ) (d : ℝ) (hd : 0 ≤ d) (i : ℝ) (he : s ≤ i) (hz : z ≤ m + n' + (n + m')) :
    d * exp (-i * r) * rope t p ^ z ≤ d * exp (-s * r) * rope t p ^ (m + n' + (n + m')) := by
    gcongr
    exact ropey t p
  exact
    add_le_add (hmul _ _ (by positivity) _ (min_le_left a b) (by omega))
      (hmul _ _ (by positivity) _ (min_le_right a b) (by omega))

lemma Handles.main_mul (h : Tames T F) (h' : Tames T H) : Tames T (F * H) := by
  refine ⟨?_, Holds.main_mul h h'⟩
  obtain ⟨C, hC, n, Hx⟩ := h.1
  obtain ⟨D, hD, m, U⟩ := h'.1
  refine ⟨C * D, by positivity, n + m, fun x t p => ?_⟩
  have ht := ropey0 t p
  simp only [Pi.mul_apply, Pi.one_apply, mul_one] at *
  rw [norm_mul]
  exact
    (mul_le_mul (Hx ..) (U ..) (norm_nonneg _) (by positivity)).trans_eq
      (by
        rw [pow_add]
        ring)

lemma Handles.main_add (h : Tames T F) (h' : Tames T H) : Tames T (F + H) :=
  ⟨h.1.add h'.1 ropey (fun _ => zero_le_one), h.2.add h'.2 ropey (fun _ => zero_le_one)⟩

lemma Sticky.main_sum (U : Finset J) {f : J → Profile X E} (hf : ∀ i ∈ U, Sticky T (f i)) :
    Sticky T (∑ i ∈ U, f i) :=
  Holds.p_sum U hf ropey (fun _ => zero_le_one)

lemma Handles.main_sum (U : Finset J) {f : J → Profile X E} (hf : ∀ i ∈ U, Tames T (f i)) :
    Tames T (fun x t p => ∑ i ∈ U, f i x t p) :=
  Handles.lsum U hf ropey (fun _ => zero_le_one)
section CLM
variable [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma hefty_le (L : E →L[ℝ] Y) (p : E) : heft (L p) ≤ (1 + ‖L‖) * heft p := by
  unfold heft
  nlinarith [L.le_opNorm p, norm_nonneg L, norm_nonneg p]

lemma clone {F : Profile X Y} (h : Vouch F) (L : E →L[ℝ] Y) : Vouch (fun x t p => F x t (L p)) := by
  obtain ⟨C, hC, n, h⟩ := h
  refine ⟨C * (1 + ‖L‖) ^ n, by positivity, n, fun x t p => ?_⟩
  refine (h x t (L p)).trans ?_
  rw [rope_exp, rope_exp]
  simp only [Pi.one_apply, mul_one]
  have hz := hefty0 (L p)
  calc
    _ ≤ C * (exp (n * |t|) * ((1 + ‖L‖) * heft p) ^ n) := by
      gcongr
      exact hefty_le ..
    _ = _ := by
      rw [mul_pow]
      ring
end CLM
end regular
end YM.WilsonMS.Climb
