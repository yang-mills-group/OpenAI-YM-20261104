import YM.WilsonMS.Regulator.UpperCharges
/-!
# Taking the cheap finite difference through Vane `Cabin` and loop

Carry polynomial costs in the incoming *chart* not just pointwise. Never
assume a formal functional integral. For SatC/SatP (line integral at every
fixed choice of remaining arguments, including negative shell times) take
either east or West line bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real Finset
open MS MS.Plane MS.Landau MS.Landau.Detect MS.Land MS.Heat MS.Tone MS.Koszul
open MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Book MS.Osc MS.Osc.Snap MS.Vane MS.City MS.Dial MS.Tide
open MS.Local.Physical Wire Belt Geo Flux
variable {G : Gauge} {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open scoped ContDiff

lemma bill_lip (p q r : QP) : ‖Tone.bill p r - Tone.bill q r‖ ≤ 4 * ‖r‖ * ‖p - q‖ := by
  rw [Tone.rights p, Tone.rights q, Fiddle.bill_at, Fiddle.bill_at]
  have h (p : ℝ) : ‖fderiv ℝ Fiddle.bellZ p‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_one] using Fiddle.wall_x 1 p
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (Fiddle.W_tip r) (norm_nonneg (p - q)))
  calc
    _ ≤ 1 * ‖Fiddle.Aux r p - Fiddle.Aux r q‖ :=
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
        (fun p _ => Fiddle.bellZ_p.differentiable (by decide) p) (fun p _ => h p) trivial trivial
    _ ≤ _ := by
      rw [one_mul, ← map_sub]
      exact ContinuousLinearMap.le_opNorm ..
variable {T : X → X → ℝ → Prop} {F H : Glade G X}

omit [NormedSpace ℝ E] in
lemma scatter_p {A : Type} (S : Sector A) (w : Legs A) {f : X → ℝ → E → Shared A ℂ}
    (he : ∀ l r, Split l r w → Tames T (fun x t p => f x t p l r)) :
    Tames T (fun x t p => scatter S w (f x t p)) := by
  induction w generalizing f with
  | nil => exact he _ _ .nil
  | cons i w ih =>
    exact
      ih
        (fun l r h =>
          Handles.main_add (he _ _ h.left) (Handles.main_mul (Handles.point _) (he _ _ h.right)))
variable {τ : X → QP}

def Stride (T : X → X → ℝ → Prop) (τ : X → QP) :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x y r, 0 ≤ r → T x y r → ‖τ x - τ y‖ ≤ B * exp (-r)

lemma Stride.phase (h : Stride T τ) (L : E →L[ℝ] QP) :
    Tames T (fun i (_ : ℝ) p => Tone.bill (τ i) (L p)) := by
  obtain ⟨C, hC, H⟩ := h
  refine ⟨⟨1, zero_le_one, 0, fun x t p => ?_⟩, 1, zero_lt_one, 4 * ‖L‖ * C, by positivity, 1, ?_⟩
  · rw [Tone.bill_norm]
    simp
  intro x y r hr hs t p
  apply (bill_lip ..).trans
  have hz : ‖p‖ ≤ rope t p := by
    refine
      le_trans (b := heft p) (by simp [heft])
        (le_mul_of_one_le_left (hefty0 p).le (Real.one_le_exp (by positivity)))
  have he := L.le_opNorm p
  have hu := H _ _ _ hr hs
  calc
    _ ≤ 4 * (‖L‖ * rope t p) * (C * exp (-r)) := by
      have he := he.trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
      have ht := ropey0 t p
      gcongr
    _ = _ := by
      rw [neg_one_mul]
      simp only [pow_one, Pi.one_apply]
      ring
variable {W : Type} [LinearOrder W] {A : Deck G} {M : Booked A} {L : MS_Data G M} {x : Position W X}
  {U : Rake.Dance G X W} {f : W → Rake.Label A} {μ : ℝ} {R S : Finset W} {m n k : ℕ}
set_option quotPrecheck false
local notation "Rρ" => frameF X μ
local notation "Ζ" => constantP G X (PlanetD G)

abbrev Pool (T : X → X → ℝ → Prop) (F : Glade G X) :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wired G E), Sticky T (liftC F w)

abbrev PoolP (T : X → X → ℝ → Prop) (F : Glade G X) :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wired G E),
    w.length > 0 → Tames T (liftC F w)
variable (ht : Mesh (frameF X μ) x) (h : DOrd M (frameF X μ) L f x U)
include ht h

lemma Holds.pyramid (hs : S.Nonempty) (n : ℕ) (hF : Pool T (U S n)) : PoolP T (U S n) :=
  fun E _ _ l hx => ⟨Climb.pyramid ht h hs n l hx, hF E l⟩

lemma allSat (hs : S.Nonempty) (hr : R.Nonempty) (m n : ℕ) (x' : X) (t : ℝ) (p : QP) :
    SatP planeF (PlanetD G t) (U S n x' t) (U R m x' t) p := by
  let B := Rake.builder L ht f
  rcases le_total t 0 with ht | hu
  · obtain ⟨K, hK⟩ := tip0 B h (n := n) hs
    obtain ⟨J, hJ⟩ := tip0 B h (n := m) hr
    let q := slotL (v := μ) ht x'
    exact priceP B.ground.well hK.2.2 hJ.2.2 (beacon _) q p
  let q : Vane.Vista Rρ := ⟨x', t, hu⟩
  have hw := Architect (b := L) f _ (westV (P := Rρ))
  have he := Architect (b := L) f _ (gulfG (P := Rρ))
  exact priceP hw.χ (farther B he hw h hs n) (farther B he hw h hr m) (beacon _) q p

lemma allCycle (hs : S.Nonempty) (n : ℕ) (x' : X) (t : ℝ) :
    SatC planeF (PlanetD G t) (U S n x' t) false := by
  let B := Rake.builder L ht f
  rcases le_total t 0 with he | hu
  · obtain ⟨K, hK⟩ := tip0 B h (n := n) hs
    let q := slotL (v := μ) he x'
    exact
      herec (beacon _) B.ground.well hK.2.2 (fun _ => zero_le_one) (fun _ => by apply Latch.length_p)
        q
  have hv := Architect (b := L) f _ (westV (P := Rρ))
  exact
    herec (beacon _) hv.χ (farther B (Architect f _ (gulfG (P := Rρ))) hv h hs n)
      (fun _ => zero_le_one) (FarBasis _ _ _) (show Vane.Vista Rρ from ⟨x', t, hu⟩)

local notation "ΔQ" => sailP (fun (_ : X) => planeF) Ζ

lemma cycleHeld (hs : S.Nonempty) (n : ℕ) (w : Wired G E)
    (hv :
      ∀ (F' : Type) [NormedAddCommGroup F'] [NormedSpace ℝ F'] (l : Wired G F'),
        w.length < l.length → Sticky T (liftC (U S n) l)) :
    Tames T (liftC (ΔQ (U S n)) w) := by
  let q : QP × E →L[ℝ] QP := ContinuousLinearMap.fst ℝ QP E
  let p : QP × E →L[ℝ] E := ContinuousLinearMap.snd ℝ QP E
  let v := Wire.lift w p
  let F := U S n
  let Y : Profile X (QP × E) := fun x t y => trc (PlanetD G t) y.1 (F x t) (sail w y.2)
  have hh : Winter T Y := by
    unfold Y
    simp_rw [at_trc]
    refine
      Handles.lsum Finset.univ
        (fun i hi =>
          Handles.lsum Finset.univ (fun j hj => ?_) (fun t p => ropey t p.2)
            (fun p => (skin_p p.1).le))
        (fun t p => ropey t p.2) (fun p => (skin_p p.1).le)
    let u := (i, q) :: (j, -q) :: v
    have hu : w.length < u.length := by simp [u, v]
    have he : Tames T (liftC (U S n) u) := ⟨pyramid ht h hs n u (by omega), hv (QP × E) u hu⟩
    have hH := Planet_pair he i j
    unfold liftC u v at hH
    simp only [sail_cons, lift_sail] at hH
    exact hH
  change Tames T (fun i t p => ∫ q, Y i t (q, p) ∂planeF)
  exact
    Winter.rescue hh (fun i t p => allCycle ht h hs n i t (sail w p) (fun i => Bool.noConfusion i))

lemma CabinHeld (hp : Stride T τ) (hs : S.Nonempty) (hr : R.Nonempty) (hF : PoolP T (U S n))
    (hH : PoolP T (U R m)) (w : Wired G E) :
    Tames T (liftC (regionC (fun _ => planeF) τ Ζ (U S n) (U R m)) w) := by
  let F := U S n
  let H := U R m
  unfold liftC regionC Cabin
  simp_rw [sail_scatter]
  refine scatter_p _ _ (fun l r hl => ?_)
  simp_rw [sail_net]
  refine
    Handles.main_mul (hp.phase (net l))
      (Handles.main_sum Finset.univ (fun i hi => Handles.main_sum Finset.univ (fun j hj => ?_)))
  let Y : Profile X (QP × E) := fun x' t p =>
    Tone.bill (τ x') p.1 * meshZ (PlanetD G t) i j (F x' t) (H x' t) (sail l p.2) (sail r p.2) p.1
  suffices hv : Winter T Y from
    Winter.rescue hv (fun x t p => allSat ht h hs hr m n x t (τ x) i j (sail l p) (sail r p))
  rw [show
      Y =
        (fun x t (p : QP × E) =>
          PlanetD G t i j p.1 *
            ((Tone.bill (τ x) p.1 * (2 * cross (parity j) (degree (field parity) l))) *
                F x t ((i, p.1) :: sail l p.2) *
              H x t ((j, -p.1) :: sail r p.2)))
      from ?_]
  swap
  · funext x t p
    unfold Y meshZ
    rw [sail_degree]
    ring
  let q := ContinuousLinearMap.fst ℝ QP E
  let p := ContinuousLinearMap.snd ℝ QP E
  have H₁ : Tames T (fun i' t (x : QP × E) => F i' t ((i, x.1) :: sail l x.2)) := by
    convert hF (QP × E) ((i, q) :: Wire.lift l p) (by simp) using 1
    funext x t y
    simp [liftC, F, q, p]
  have H₂ : Tames T (fun i t (x : QP × E) => H i t ((j, -x.1) :: sail r x.2)) := by
    convert hH (QP × E) ((j, -q) :: Wire.lift r p) (by simp) using 1
    funext x t y
    simp [liftC, H, q, p]
  exact
    Planet_pair
      (Handles.main_mul (Handles.main_mul (Handles.main_mul (hp.phase q) (Handles.point _)) H₁) H₂) _
      _

omit ht h in
lemma ex_tree (hn : 0 < n) (u : PoolP T H) (f : W → Rake.Label A) (w : Wired G E) :
    Tames T (liftC (expJ Ζ (approach Rρ L n) H) w) := by
  let F := approach Rρ L n
  unfold liftC expJ tree
  simp_rw [sail_scatter]
  refine scatter_p _ _ (fun l r hl => ?_)
  simp_rw [attaches, sail_net, sail_degree]
  let q := net l
  refine Handles.main_sum Finset.univ (fun i _ => Handles.main_sum Finset.univ (fun j _ => ?_))
  have hE (i j : BH G) (q : E →L[ℝ] QP) : Tames T (fun (_ : X) t p => PlanetD G t i j (q p)) :=
    ⟨clone (Planet_tame (T := T) i j).1 _, holding _⟩
  have hm (i : BH G) : Tames T (liftC F ((i, -q) :: l)) :=
    ⟨locked f _ (by simp [q]) (by simp) _ hn,
      by
      unfold F liftC approach circle nameR frameF
      dsimp only
      exact holding _⟩
  exact
    Handles.main_add
      (Handles.main_mul (hE i j (-q))
        (Handles.main_mul (Handles.main_mul (Handles.point _) (hm i))
          (u E ((j, - -q) :: r) (by simp))))
      (Handles.main_mul (hE _ _ (- -q))
        (Handles.main_mul (Handles.main_mul (Handles.point _) (hm _))
          (u E ((i, - -q) :: r) (by simp))))
end YM.WilsonMS.Climb
