import YM.WilsonMS.Calibration.StrongWind
/-!
# Adapt `Rake.Sequence` certificate to new input. Then use actual continuum.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind
  Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily
  Program
open scoped Topology ContDiff Interval

variable {I W : Type} {G : Gauge}
local notation "Qb" => Ensure.deck G
variable {K : Belt I} {O : Booked (Ensure.deck G)} (V : BasisMenu G) (P : Geo I)
  (T : Prescription (Ensure.deck G)) (M : MS_Data G O)

def markRow (x : Label Qb) : Site G I :=
  circle P.η (col (rowFull V T.team (T.fees x.h x.item)))

lemma VenLight (h : G.Simple) (x : Label Qb) :
    Ven (fun _ => planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G)) (initials P T)
      (markRow V P T x) := by
  let B := skyline G T.team
  let A := T.fees x.h x.item
  let H := rowFull V T.team A
  obtain hP := Marked.law (mark_seekW V (d := x.h) (p := T.team) h) A
  let Q := seekW V T.team x.h
  have hG := hP.road
  change Domain.Flow _ _ _ _ _ (Wind.col H) at hG
  have hh (i : ℕ) : Wind.Fees false 0 (H i) := (feeds V T.team A).owes i
  intro n
  refine ⟨nameWarm (H n) (hh n), fun i w t => ?_⟩
  obtain hv := pour (spaceL G) hG (P.η i) w n t
  rw [ergo (η := P.η)] at hv
  let z := exp t
  let f := H n (P.η i)
  have he :
    sailP (fun _ => μzone) (constantP G I (LowP G)) (markRow V P T x n) i t =
      cycle (PlanetL G t) planeF (f z) :=
    (startCycle f 0 (hh n |>.stay (P.η i)) _ _).symm
  rw [show sailP (fun _ => (spaceL G).measure) _ (circle _ (col H) n) i t = _ from he] at hv
  exact hv

lemma sofar (x : Label Qb) (k : ℕ) : Tip P true false x.h (markRow V P T x k) := by
  obtain h : Fees false 0 _ := (feeds V T.team (T.fees x.h x.item)).owes k
  exact ⟨collectFee h, nameWarm _ h, Lease.sticks (sunX P _ h) (fun i => rank_e P i x.h)⟩

lemma plots (p : W → Label Qb) (h : Installed V M T) (hv : Gold P K) :
    Arch K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (initials P T) (markRow V P T ∘ p)
        (Label.h ∘ p) ∧
      Arch K (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (rowM P M ∘ p)
          (Label.h ∘ p) ∧
        ArcS K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (constantP G I (PlanetD G))
          (constantP G I (PlanetD G)) (initials P T) (approach P M) (markRow V P T ∘ p) (rowM P M ∘ p)
          (Label.h ∘ p) := by
  let S := K.price
  have hb (n : ℕ) (he : 0 < n) := partials hv (show 1 ≤ n from he) (fun r hr => h.bulk n he r hr)
  have H (i : W) (n : ℕ) :=
    partials hv (show 0 ≤ n from Nat.zero_le n)
      (fun r hr => (h.mark (p i |>.h) (p i |>.item)) n (Nat.zero_le _) r hr)
  have he i : 1 ≤ K.price.length i := hv.day i ▸ Real.one_le_exp (hv.paid i)
  have hx := cost_D (G := G) hv.day
  exact
    ⟨⟨CoupleY he hv.day, Mate0 he hv.day, fun i hi => (hb i hi).1, fun i n => (H i n).1⟩,
      ⟨fun i j => polar (hx i j), hx, fun i hi => (hb i hi).2.1, fun i n => (H i n).2.1⟩,
      ⟨submarineT he hv.day (phaseY hv), submarineP he hv.day (phaseY hv), fun i hi => (hb i hi).2.2,
        fun i n => (H i n).2.2⟩⟩

open Vane
variable [LinearOrder W] {x : Rake.Position W I}

abbrev AboveOrd (V : BasisMenu G) (P : Geo I) (T : Prescription Qb) (R : W → Label Qb)
    (x : Rake.Position W I) (U : Dance G I W) :=
  Fields x (fun (_ : I) => planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G)) (initials P T)
    (markRow V P T ∘ R) U

theorem covers (R : W → Label Qb) (h : G.Simple) (hx : Mesh P x) (he : Installed V M T) :
    ∃ U V',
      AboveOrd V P T R x U ∧
        DOrd O P M R x V' ∧
          ∀ S : Finset W,
            S.Nonempty →
              ∀ n : ℕ,
                let k := charge (Label.h ∘ R) S;
                Verdict P k 0 (U S n) ∧
                  Verdict P k 0 (V' S n) ∧ Verdict P k eps_gain (U S n - V' S n) := by
  obtain ht :=
    (show
      Tour (constantP G I (LowP G)) (constantP G I (PlanetL G)) P x true (initials P T)
        (markRow V P T ∘ R) (Label.h ∘ R)
      from
      ⟨hx, Geo.masterL .., fun _ _ => tagL P T _, fun _ _ => sofar .., fun _ => VenLight V P T h _⟩)
  obtain hV := builder M hx R
  obtain ⟨U, hU⟩ := formal ht
  obtain ⟨W, hW⟩ := formal hV
  obtain ⟨Z, X, Tz⟩ := plots V P T M R he (gulfG (P := P))
  obtain ⟨Y, Q, RQ⟩ := plots V P T M R he (westV (P := P))
  exact
    ⟨U, W, hU, hW, fun _ hp n =>
      ⟨closure ht Z Y hU hp n, closure hV X Q hW hp n, trade ht hV Z X Y Q Tz RQ hU hW hp n⟩⟩
end YM.WilsonMS.BMenu
