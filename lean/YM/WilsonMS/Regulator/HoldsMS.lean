import YM.WilsonMS.Regulator.RiverHolds
/-!
# Quantitative continuity for `Dial.tour` / MS-bar positions

Arbitrary continuum shapes at mutual distances in fixed compact ranges. In
particular, will let us directly integrate smooth tests with residual rate at
the freed physical end. No Born-only assumption. Explicit about UV and IR
passes; small Hölder exponent allowed separately for every mark list and
every perturbative order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real Finset
open MS MS.Plane MS.Landau MS.Landau.Detect MS.Land MS.Heat MS.Tone MS.Koszul
open MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Book MS.Osc MS.Osc.Snap MS.Vane MS.City MS.Dial MS.Tide
open MS.Local.Physical Wire Belt Geo Flux
variable {G : Gauge} {X : Type} {F : Glade G X}
variable {W : Type} [LinearOrder W] {A : Deck G} {M : Booked A} {L : MS_Data G M} {x : Position W X}
  {U : Rake.Dance G X W} {f : W → Rake.Label A} {μ : ℝ} {R S : Finset W} {m n k : ℕ}

/-- The precision of a position displacement (in physical log-units). -/
def stepCost (x : Position W X) (i j : X) (r : ℝ) :=
  ∀ w, ‖x w i - x w j‖ ≤ exp (-r)
local notation "𝔇" => stepCost x
set_option quotPrecheck false
local notation "Rρ" => frameF X μ
local notation "Ζ" => constantP G X (PlanetD G)
local notation "mρ" => (fun (_ : X) => planeF)

lemma stepT (hp : S.Nonempty) (hs : R.Nonempty) : Stride 𝔇 (rootX x S - rootX x R) := by
  refine ⟨2, by norm_num, fun i j r hr h => ?_⟩
  rw [rootX, rootX, dif_pos hp, dif_pos hs]
  simp only [Pi.sub_apply]
  rw [sub_sub_sub_comm]
  exact (norm_sub_le ..).trans ((add_le_add (h _) (h _)).trans_eq (by rw [two_mul]))
variable (ht : Mesh (frameF X μ) x) (h : DOrd M (frameF X μ) L f x U)
include ht h

lemma gatherSource (hp : S.Nonempty) (hu : ∀ i ⊂ S, ∀ n, Pool 𝔇 (U i n))
    (hz : ∀ i < n, Pool 𝔇 (U S i)) : Pool 𝔇 (Src x mρ Ζ Ζ (approach Rρ L) U S n) := by
  intro E _ _ w
  unfold Src multi lonely liftC
  simp only [Pi.add_apply, Finset.sum_apply]
  refine
    (Handles.main_add (Handles.main_sum _ (fun i hi => ?_))
        (Handles.main_sum _ (fun i hi => Handles.main_sum _ (fun j hj => ?_)))).2
  · have he := Finset.mem_Ico.mp hi |>.2
    exact ex_tree (by omega) (Holds.pyramid ht h hp i (hz i he)) f w
  obtain ⟨hb, hV, hH, H⟩ := n_small hi
  exact
    CabinHeld ht h (stepT hV hp) hV hH (Holds.pyramid ht h hV _ (hu _ hb _))
      (Holds.pyramid ht h hH _ (hu _ H _)) w

lemma ascent (S : Finset W) (n : ℕ) : Pool 𝔇 (U S n) := by
  induction S using Finset.strongInductionOn generalizing n with
  | _ S ih =>
    obtain he | hp := S.eq_empty_or_nonempty
    · rw [he, h.1]
      exact fun E _ _ l => hold0
    by_cases hv : 2 ≤ S.card
    swap
    · obtain ⟨i, hi⟩ :=
        Finset.card_eq_one.mp
          (show S.card = 1 from by
            obtain hh := Finset.card_pos.mpr hp
            omega)
      rw [hi, h.2.1]
      intro E _ _ w
      unfold liftC
      dsimp only [rowM, circle, nameR, frameF, Function.comp_apply]
      exact holding _
    induction n using Nat.strong_induction_on with
    | h n hb =>
      let Q := rhs x mρ Ζ Ζ (approach Rρ L) U S n
      have ht' := h.2.2 S hv n
      have hxQ : U S n = river Q := ht'.2.2
      obtain H := Dial.source f ht h (n := n) hv
      have hQ := emerged (Rake.builder L ht f) h hv n
      have hW := CameZ hQ
      have he : Came Rρ false Q := ⟨hW.1.add H.1, collect_p hW.2 H.2⟩
      obtain ⟨k, hk⟩ := hQ.2
      suffices hh :
        ∀ j : ℕ,
          ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wired G E),
            k < j + w.length → Sticky 𝔇 (liftC (U S n) w)
        from fun E _ _ w => hh (k + 1) E w (by omega)
      intro j
      induction j with
      | zero =>
        intro E _ _ w hw
        rw [show liftC (U S n) w = 0 from
            funext fun x =>
              funext fun t =>
                funext fun p =>
                  hk _ _ _ (by exact_mod_cast (show k < (sail w p).length from (by simpa using hw)))]
        exact hold0
      | succ j ih' =>
        intro E _ _ w hw
        rw [hxQ]
        exact
          riverHeld he ht'.2.1 w
            ((cycleHeld ht h hp n w (fun t _ _ l hl => ih' t l (by omega))).2.add
              (gatherSource ht h (n := n) hp ih hb E w) ropey (fun _ => zero_le_one))
omit ht h
open Vane Puff Puff.Actors Puff.Engine Puff.SplitP Puff.Mom
variable {T : X → X → ℝ → Prop} {u : ℕ}

lemma Far_quarter (hp : Verdict Rρ u 0 F) :
    ∃ A : ℝ,
      0 ≤ A ∧ ∀ (t : ℝ), 0 ≤ t → ∀ x, ‖Vane.blade F x - F x t []‖ ≤ A * exp (-(1 / 4 : ℝ) * t) := by
  obtain ⟨C, hC, k, hk⟩ := hp.2.1
  obtain ⟨D, hD, hh⟩ := capped High.p_gain k
  refine ⟨C * (1 + |μ|) ^ k * D, by positivity, fun t ht x => ?_⟩
  refine (hk (show Vane.Vista Rρ from ⟨x, t, ht⟩)).trans ?_
  change
    C * ((1 + |μ|) * (1 + |t|)) ^ k * (exp ((-(u : ℝ) - 0) * 0) * exp (-High.eps_gain * (t - 0))) ≤ _
  rw [abs_of_nonneg ht, sub_zero, sub_zero, mul_zero, exp_zero, one_mul, mul_pow]
  refine
    le_trans (le_of_eq (b := C * (1 + |μ|) ^ k * ((1 + t) ^ k * exp (-High.eps_gain * t))) (by ring))
      ?_
  exact
    (mul_le_mul_of_nonneg_left (hh t ht) (by positivity)).trans_eq
      (by
        unfold High.eps_gain
        ring_nf)

abbrev Traced (T : X → X → ℝ → Prop) (F : X → ℂ) :=
  Tames T (fun x (_ _ : ℝ) => F x)

lemma Traced.exported {T} {F : X → ℂ} (h : Traced T F) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖F x‖ ≤ C) ∧
      ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ x y r, 0 ≤ r → T x y r → ‖F x - F y‖ ≤ D * exp (-a * r) := by
  obtain ⟨⟨C, hC, n, h⟩, a, ha, D, hD, m, hM⟩ := h
  have he : rope 0 (0 : ℝ) = 1 := by simp [rope, heft]
  exact
    ⟨⟨C, hC, fun x => by simpa only [he, one_pow, Pi.one_apply, mul_one] using h x 0 0⟩, a, ha, D, hD,
      fun x y r hp hi => by simpa only [he, one_pow, Pi.one_apply, mul_one] using hM _ _ _ hp hi 0 0⟩

lemma vertical (h : Pool T F) (hv : Verdict Rρ u 0 F) : Traced T (Vane.blade F) := by
  obtain ⟨U, hU, hu⟩ := Far_quarter hv
  obtain ⟨a, ha, D, hD, n, he⟩ := h ℝ []
  let v : ℝ := n
  have hh : 0 ≤ v := Nat.cast_nonneg _
  let k := a / 2 / (v + 1)
  have h0 : 0 < k := by
    unfold k
    positivity
  have hk : k * (v + 1) = a / 2 := div_mul_cancel₀ _ (by positivity)
  let b := min (k / 4) (a / 2)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  refine ⟨?_, b, hb, U + D + U, by positivity, 0, fun x y r hr hE s p => ?_⟩
  · obtain ⟨C, hC, m, hM⟩ := hv.2.2
    refine ⟨C * (1 + |μ|) ^ m, by positivity, 0, fun x t p => (hM x).trans ?_⟩
    simp [moneyX, tarB, habitat]
  let t := k * r
  have ht : 0 ≤ t := by
    unfold t
    positivity
  have hz : ‖F x t [] - F y t []‖ ≤ D * exp (-a * r + v * t) := by
    apply le_trans (he x y r hr hE t 0)
    simp only [Pi.one_apply, mul_one, rope_exp, norm_zero, heft, add_zero, one_pow, abs_of_nonneg ht,
      Real.exp_add]
    exact le_of_eq (mul_assoc ..)
  have hV : exp (-(1 / 4 : ℝ) * t) ≤ exp (-b * r) := by
    apply exp_monotone
    unfold t
    have he : b ≤ k / 4 := min_le_left ..
    nlinarith
  have hF : exp (-a * r + v * t) ≤ exp (-b * r) := by
    apply exp_monotone
    unfold t
    have he : b ≤ a / 2 := min_le_right ..
    have hp := congr_arg (· * r) hk
    nlinarith
  have hL := dist_triangle4 (Vane.blade F x) (F x t []) (F y t []) (Vane.blade F y)
  rw [dist_comm (F y t []) (Vane.blade F y)] at hL
  simp only [dist_eq_norm] at hL
  rw [pow_zero, Pi.one_apply, mul_one, mul_one]
  have hu' (x : X) := (hu _ ht x).trans (mul_le_mul_of_nonneg_left hV hU)
  have hz := hz.trans (mul_le_mul_of_nonneg_left hF hD)
  linarith [hu' x, hu' y]

include ht h in
lemma traced_B (S : Finset W) (n : ℕ) : Traced 𝔇 (fun i => book L f μ (pointI x i) S n) := by
  simp_rw [← Point_t L f μ ht h]
  obtain hh | hp := S.eq_empty_or_nonempty
  · subst S
    simp_rw [Fleet.toZ, h.1, Pi.zero_apply,
      show Vane.blade (0 : Glade G X) = 0 from funext (fun i => (Fleet.allow_zero i).2)]
    exact Handles.point (E := ℝ) 0
  exact vertical (ascent ht h S n) (reports f ht h hp n)
open Book.Convolve
variable {F H : X → Finset W → Convolve.T ℂ}

def BoundClock (R : X → X → ℝ → Prop) (F : X → Finset W → Convolve.T ℂ) :=
  ∀ S n, Traced R (fun i => F i S n)

lemma BoundClock.prod (hF : BoundClock T F) (hH : BoundClock T H) :
    BoundClock T (fun i => (Trunk.stack (marked W)).core (F i) (H i)) := by
  intro s n
  unfold Traced
  change Tames T (fun i (_ p : ℝ) => (∑ d ∈ subs s, Trunk.core (F i d.1) (H i d.2)) n)
  simp_rw [Finset.sum_apply]
  exact
    Handles.main_sum _
      (fun j hj => Handles.main_sum _ (fun i hi => Handles.main_mul (hF _ _) (hH _ _)))

lemma decayedMS (hF : BoundClock T F) : BoundClock T (fun i => bouquet (F i)) := by
  let P := Trunk.stack (marked W)
  have he (k : ℕ) : BoundClock T (fun i => P.power (F i) k) := by
    induction k with
    | zero =>
      intro s n
      exact Handles.point _
    | succ k ih => exact hF.prod ih
  intro s n
  unfold bouquet Cheer Actors.cheers Traced
  simp_rw [Finset.sum_apply]
  exact Handles.main_sum _ (fun i _ => Handles.main_mul (Handles.point _) (he i s n))
include ht

/-- Quantified Hölder continuity of all MS continuum cumulants and ordinary
correlations in the positions at fixed scale. `Mesh` here is continuum
separation. No estimates near the collision diagonal. -/
lemma holderMS (f : W → Rake.Label A) (L : MS_Data G M) :
    BoundClock 𝔇 (fun i => book L f μ (pointI x i)) ∧
      BoundClock 𝔇 (fun i => tour L f μ (pointI x i)) := by
  obtain ⟨U, hU⟩ := Vane.formal (Rake.builder L ht f)
  have hv : BoundClock 𝔇 (fun i => book L f μ (pointI x i)) := fun s n => traced_B ht hU s n
  exact ⟨hv, decayedMS hv⟩
end YM.WilsonMS.Climb
