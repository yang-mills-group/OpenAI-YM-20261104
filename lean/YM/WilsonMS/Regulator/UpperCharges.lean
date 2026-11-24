import YM.WilsonMS.Regulator.LineHolds
/-!
# Individual and past-half costs on the MS comparison charts

Scale primitives for the `Glade` reading estimates. A momentum-kernel dot
comes with *every* matching polynomial derivative; can eventually choose a
larger power and common constant for every finite set of costed wires and
orders. Here produce the Hölder prices on the individual slices, before the
programme of `HoldsMS` (which will cover full position arrays).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real
open MS MS.Plane MS.Land
open MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job
open MS.Rake MS.Orbit MS.Book MS.Osc MS.Osc.Snap MS.Vane MS.City MS.Dial MS.Tide
open MS.Local.Physical Wire Belt Geo
variable {G : Gauge} {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : X → X → ℝ → Prop}

abbrev Wired (G : Gauge) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Wire (BH G) E QP

def liftC (F : Glade G X) (w : Wired G E) : Profile X E := fun x t p => F x t (sail w p)
variable {F : Glade G X} {μ : ℝ} {K : Belt X} {z : ℤ} {w : Wired G E}
set_option quotPrecheck false
local notation "Rρ" => frameF X μ
local notation "J" => PlanetD G

omit [NormedSpace ℝ E] in
lemma cheapC (t μ : ℝ) (p : E) :
    (1 + |μ|) * (1 + |t|) * (1 + exp t * ‖p‖) ≤ (1 + |μ|) * rope t p ^ 2 := by
  have hp := hefty p
  have hz := ropey t p
  have he : 1 + |t| ≤ rope t p :=
    le_trans (by linarith only [Real.add_one_le_exp (|t|)])
      (show exp |t| ≤ rope t p from le_mul_of_one_le_right (exp_pos _).le hp)
  have ht : 1 + exp t * ‖p‖ ≤ rope t p := by
    unfold rope heft
    rw [mul_add, mul_one]
    exact
      add_le_add (Real.one_le_exp (by positivity))
        (mul_le_mul_of_nonneg_right (exp_monotone (le_abs_self t)) (norm_nonneg _))
  rw [mul_assoc, pow_two]
  gcongr

lemma charged {K : Belt X} (hv : ∀ p : K.time, K.price.length p = exp (tstart p))
    (hw : ∀ p : K.time, K.price.basic p = (1 + |μ|) * (1 + |tstart p|))
    (h : Cape K.price (plug F) (rateS K z) w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x t, t ∈ K.slot x → ∀ p, ‖liftC F w x t p‖ ≤ C * rope t p ^ n := by
  obtain ⟨C, hC, n, h⟩ := h.norm_cost
  let k := n * 2 + (pitch w - z).natAbs
  let M : ℝ := 1 + |μ|
  have hM : 1 ≤ M := by simp [M]
  refine ⟨C * M ^ n, by positivity, k, ?_⟩
  intro x t ht p
  let q : K.time := ⟨x, t, ht⟩
  have hx := h q p trivial
  have hV := ropey t p
  have hh := hv q
  have hT : tstart q = t := rfl
  rw [hT] at hh
  have hP : K.price.full.cheap q p = M * (1 + |t|) * (1 + exp t * ‖p‖) := by
    simp only [Scale.full, Scale.weight, hh, hw q, hT]
    rfl
  have hQ : (exp t) ^ (pitch w - z) ≤ rope t p ^ (pitch w - z).natAbs := by
    rw [rope_exp]
    exact (price_zpow ..).trans (le_mul_of_one_le_right (exp_pos _).le (one_le_pow₀ (hefty p)))
  apply hx.trans
  dsimp only
  rw [rateS, hP, hh, ← zpow_add₀ (exp_pos t).ne', ← sub_eq_add_neg]
  have hu := zpow_nonneg (exp_pos t).le (pitch w - z)
  calc
    _ ≤ C * (M * rope t p ^ 2) ^ n * rope t p ^ (pitch w - z).natAbs := by
      gcongr C * ?_ ^ n * ?_
      exact cheapC t μ p
    _ = _ := by
      unfold k
      rw [pow_add, Nat.mul_comm n, pow_mul, mul_pow]
      ring

lemma allC (hu : Cape (east Rρ false).price (plug F) (rateS (east Rρ false) z) w)
    (hv : Cape (West Rρ).price (plug F) (rateS (West Rρ) z) w) : Vouch (liftC F w) := by
  obtain ⟨C, hC, n, hp⟩ := charged (K := east Rρ false) (μ := μ) (fun p => coldE ..) (fun _ => rfl) hu
  obtain ⟨D, hD, m, h⟩ := charged (K := West Rρ) (μ := μ) (fun _ => rfl) (fun _ => rfl) hv
  refine ⟨max C D, hC.trans (le_max_left ..), max n m, ?_⟩
  intro x t p
  have hr := ropey0 t p
  rw [Pi.one_apply, mul_one]
  rcases le_total t 0 with ht | ht
  · exact
      (hp x t ht p).trans
        (by
          gcongr
          exact le_max_left ..
          exact ropey ..
          exact le_max_left ..)
  exact
    (h x t ht p).trans
      (by
        gcongr
        exact le_max_right ..
        exact ropey ..
        exact le_max_right ..)

lemma prepC {z' : ℤ} (hu : Cape (east Rρ false).price (plug F) (rateS (east Rρ false) z) w)
    (hv : Cape (West Rρ).price (plug F) (rateS (West Rρ) z') w) : Vouch (liftC F w) := by
  obtain ⟨C, hC, n, hp⟩ := charged (K := east Rρ false) (μ := μ) (fun p => coldE ..) (fun _ => rfl) hu
  obtain ⟨D, hD, m, h⟩ := charged (K := West Rρ) (μ := μ) (fun _ => rfl) (fun _ => rfl) hv
  refine ⟨max C D, hC.trans (le_max_left ..), max n m, ?_⟩
  intro x t p
  have hr := ropey0 t p
  rw [Pi.one_apply, mul_one]
  rcases le_total t 0 with ht | ht
  · exact
      (hp x t ht p).trans
        (by
          gcongr
          exact le_max_left ..
          exact ropey ..
          exact le_max_left ..)
  exact
    (h x t ht p).trans
      (by
        gcongr
        exact le_max_right ..
        exact ropey ..
        exact le_max_right ..)
variable {W : Type} [LinearOrder W] {A : Deck G} {M : Booked A} {L : MS_Data G M}
  {f : W → Rake.Label A} {x : Position W X} {U : Rake.Dance G X W}

lemma locked (f : W → Rake.Label A) (w : Wired G E) (hw : net w = 0) (hz : 0 < w.length) (n : ℕ)
    (hn : 0 < n) : Vouch (liftC (approach Rρ L n) w) := by
  have hv := (Architect (b := L) f _ (westV (P := Rρ))).states n hn
  have ht := (tagD Rρ L n).2.2
  exact allC (ht E w (fun _ => hw) (fun _ => hz)) (hv E w (fun _ => hw) (fun _ => hz))

lemma pyramid (ht : Mesh Rρ x) (h : DOrd M Rρ L f x U) {S : Finset W} (hs : S.Nonempty) (n : ℕ)
    (w : Wired G E) (hw : 0 < w.length) : Vouch (liftC (U S n) w) := by
  let B := Rake.builder L ht f
  obtain ⟨K, hV⟩ := tip0 B h (n := n) hs
  have he :=
    farther B (Architect (b := L) f _ (gulfG (P := Rρ))) (Architect (b := L) f _ (westV (P := Rρ))) h
      hs n
  apply prepC (hV.2.2 E w (fun i => Bool.noConfusion i) (fun _ => hw)) (z' := 0)
  apply Cape.up (he E w (fun i => Bool.noConfusion i) (fun _ => hw))
  intro i
  have hz : ace (charge (Label.h ∘ f) S) 0 i = (1 : ℝ) := by
    change exp (_ * (0 : ℝ)) = 1
    rw [mul_zero, exp_zero]
  rw [far, hz, one_mul, rateS, neg_zero, zpow_zero]
  exact expoW i

lemma sepE (F : Glade G X) (h : Came Rρ false F) (w : Wired G E) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∃ k : ℕ, ∀ i t, t ≤ 0 → ∀ p, ‖liftC F w i t p‖ ≤ C * exp ((1 / 2 : ℝ) * t) * heft p ^ k := by
  obtain ⟨C, hC, n, h⟩ :=
    (h.1.pick 0 E w (fun i => Bool.noConfusion i) (fun i => Bool.noConfusion i)).norm_cost
  obtain ⟨A, hA, hS⟩ := capped zero_lt_one n
  let M : ℝ := 1 + |μ|
  refine
    ⟨C * M ^ n * A, by
      unfold M
      positivity, n, ?_⟩
  intro i t ht p
  let q : (east Rρ false).time := slotL (v := μ) ht i
  refine (h q p trivial).trans ?_
  have hz := exp_le_one_iff.mpr ht
  have hZ : (east Rρ false).price.length q = exp t := length_Ω ht i
  have hQ : (east Rρ false).price.full.cheap q p ≤ M * (1 + -t) * heft p := by
    unfold Scale.full
    dsimp only
    unfold Scale.weight
    rw [hZ, show (east Rρ false).price.basic q = M * (1 + |t|) from rfl, abs_of_nonpos ht]
    apply
      mul_le_mul_of_nonneg_left _
        (by
          unfold M
          exact mul_nonneg (by positivity) (by linarith))
    exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) hz) _
  have he : (east Rρ false).price.full.cheap q p > 0 := Cost.cheap_pos _ trivial
  dsimp only
  rw [hZ, birthTar, pow_zero, mul_one, show tstart q = t from rfl]
  have hD := hS (-t) (by linarith)
  rw [neg_mul_neg, neg_mul_neg, one_mul] at hD
  have hM : 0 < M := by
    unfold M
    positivity
  have ht' := hefty0 p
  calc
    _ ≤ C * (M * (1 + -t) * heft p) ^ n * (1 * exp t) := by
      have hL : 0 ≤ -t := by linarith
      gcongr
      exact zpow_le_one₀ (exp_pos t) hz (pitch_nn _)
    _ = C * M ^ n * ((1 + -t) ^ n * exp t) * heft p ^ n := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ C * M ^ n * (A * exp ((1 / 2 : ℝ) * t)) * heft p ^ n := by gcongr
    _ = _ := by ring
end YM.WilsonMS.Climb
