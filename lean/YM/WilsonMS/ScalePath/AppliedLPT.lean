import YM.WilsonMS.ScalePath.Schedule
import YM.WilsonMS.ScalePath.PhysicalMarks

/-!
# Instantiation with tree coefficients

Apply the supplied removals. Conclude for the *actual Wilson and Haar*
coefficients at every cutoff and every mark load, with their continuum
comparisons. One dictionary, one `MS_Data`, one (bare, cutoff-dependent)
order series of lattice parameter transformations. This is a pre-renormalized
comparison in changed columns, not yet removal in the position coupling and
position frame. `Tide.remove` and `Dial.LPT_to_MS` are usable on
arbitrary LitBook, so show the precise conclusion of each. Later users
can stick with exactly the same Prescription (see `common_outputs`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Removed
open Function Filter Set Finset Metric MeasureTheory XSpace
open MS MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Swirl MS.Swirl.Near MS.Plane MS.Koszul MS.Native
  MS.Native.Wilsonian
open MS.Tone MS.Vista MS.Fleet MS.Plane MS.Latch MS.Rake MS.Dial MS.Tide
open MS.Local.Physical MS.High MS.Menus MS.Land MS.Book MS.Book.Convolve MS.Book.Program MS.Puff
  MS.Puff.Actors MS.Puff.Mom MS.Puff.Engine
open Schedule Rescaled
open Lattice
open scoped Topology ContDiff BigOperators

lemma expects_one {P : Period} (R : P.Tree) (G : Gauge) (φ : Team) (x : ℝ) :
    expectation R G φ x 1 = 1 := by
  have h := comp_expectation R G φ x 1
  rw [XSpace.Bare.normalize_unit, Coupling.comp_unit (share φ x), Coupling.comp_unit (share φ x)] at h
  exact h

variable {W I : Type} (T : Trial I W)

abbrev safe :=
  ∀ i, 4 ≤ (dimT T.side i).val
variable (h : safe T)

abbrev islandTree (T : Trial I W) (hp : safe T) (i : I) :=
  (island T.side i (hp i)).standardTree
variable {G : Gauge} {B : Deck G} (V : LitBook B) (A : Prescription B) (u : W → Label B)

def uncut (i : I) (s : Finset W) : MS.Book.Convolve.T ℂ :=
  Coupling.read
    (normalizedReading (islandTree T h i) (T.profile.η i) V (T.head i) A (fun w => T.off w i) u s)
variable [LinearOrder W]

omit [LinearOrder W] in
lemma uncut_corner (i : I) : uncut T h V A u i ∅ = Trunk.unit := by
  unfold uncut normalizedReading
  rw [Finset.prod_empty, expects_one]
  funext n
  change PowerSeries.coeff n 1 = SplitP.refineV useN (1 : ℂ) n
  rw [PowerSeries.coeff_one, SplitP.refineV]
  split_ifs with he hh ht <;>
    first
    | rfl
    | exact (hh he).elim
    | exact (he ht).elim

/-- The connected array, finite logarithm from the same tree coefficients. -/
def tally : Terrify W I := fun s n i => Puff.Log.Meter Trunk (SplitP.marked W) (uncut T h V A u i) s n

lemma tally_zero : tally T h V A u ∅ = 0 := by
  funext n i
  exact congr_fun (Puff.Log.happy Trunk (SplitP.marked W) (uncut T h V A u i)) n

lemma totalized (i : I) (s : Finset W) : bury i s (tally T h V A u) = uncut T h V A u i s := by
  let Z := uncut T h V A u i
  exact
    congr_fun
      (Puff.Log.solve Trunk (SplitP.marked W) Z (uncut_corner T h V A u i)
        (fun _ _ _ => Submodule.mem_top))
      s

lemma tally_cut (i : I) (s : Finset W) :
    PhysicalSum G A.team (T.profile.η i) (dimT T.side i) true s (fun w => T.off w i) (T.head i)
      (ApplyM V (Stripped A.team) A u) (bury i s (tally T h V A u)) := by
  rw [totalized]
  exact adapted (islandTree T h i) (T.profile.η i) V _ A _ u s

lemma cutoff (l : Filter I) {μ : ℝ} (hv : Dial.Uses T l μ) :
    Dial.Cutoff V u T μ true A (tally T h V A u) := by
  intro i s
  rw [← hv.reality i]
  exact tally_cut ..

variable (l : Filter I) (μ : ℝ) {M : Booked B}

lemma replace_tide (D : MS_Data G M) (hv : Dial.Uses T l μ) {Z : Terrify W I} {Y}
    (H : scalePhysics T.profile M D μ A V u T.off T.head T.side true l Z Y) :
    scalePhysics T.profile M D μ A V u T.off T.head T.side true l (tally T h V A u) Y := by
  rw [show tally T h V A u = Z from
      separate V u T (cutoff T h V A u l hv) (fun i s => hv.reality i ▸ H.native i s) (tally_zero ..)
        H.empty]
  exact H

lemma replace_dial (D : MS_Data G M) (hv : Dial.Uses T l μ) {Z : Terrify W I}
    (H : coherent M D V u T μ true A l Z) : coherent M D V u T μ true A l (tally T h V A u) := by
  rw [show tally T h V A u = Z from
      separate V u T (cutoff T h V A u l hv) H.cost (tally_zero ..) H.init]
  exact H

omit [LinearOrder W]

theorem applied_tide (D : MS_Data G M) (hc : G.Simple) :
    ∃ A : Prescription B,
      TaylorOK D V A ∧
        ∀ (W I : Type) (_ : LinearOrder W) (l : Filter I) (μ : ℝ) (u : W → Label B) (T : Trial I W)
          (h : safe T),
          Dial.Uses T l μ →
            ∃ Y, scalePhysics T.profile M D μ A V u T.off T.head T.side true l (tally T h V A u) Y := by
  obtain ⟨p, hp, H⟩ := Tide.remove V D hc
  refine ⟨p, hp, fun W I _ l μ u T h hv => ?_⟩
  obtain ⟨Z, Y, hY⟩ :=
    H I W _ T.profile T.side T.head true l u T.off μ hv.total hv.reality hv.upright hv.super hv.clear
      hv.wind hv.knit
  exact ⟨Y, replace_tide T h V p u l μ D hv hY⟩

theorem applied_Dial (D : MS_Data G M) (hc : G.Simple) :
    ∃ Ξ : Prescription B,
      TaylorOK D V Ξ ∧
        ∀ (W I : Type) (_ : LinearOrder W) (P : Trial I W) (l : Filter I) (μ : ℝ) (u : W → Label B)
          (h : safe P), Dial.Uses P l μ → coherent M D V u P μ true Ξ l (tally P h V Ξ u) := by
  obtain ⟨A, hA, H⟩ := Dial.LPT_to_MS V D hc
  refine ⟨A, hA, fun W I _ T l μ u h hv => ?_⟩
  obtain ⟨Z, hZ, h⟩ := H W I _ T l μ u true hv
  exact replace_dial T _ V A u l μ D hv hZ

theorem common_outputs (D : MS_Data G M) (hc : G.Simple) :
    ∃ A : Prescription B,
      TaylorOK D V A ∧
        ∀ (W I : Type) (_ : LinearOrder W) (l : Filter I) (μ : ℝ) (u : W → Label B) (T : Trial I W)
          (h : safe T),
          Dial.Uses T l μ →
            (∃ Y, scalePhysics T.profile M D μ A V u T.off T.head T.side true l (tally T h V A u) Y) ∧
              coherent M D V u T μ true A l (tally T h V A u) := by
  obtain ⟨p, hp, H⟩ := applied_tide V D hc
  refine ⟨p, hp, fun W I _ l μ u T h hv => ⟨H _ _ _ l μ u T h hv, ?_⟩⟩
  obtain ⟨Z, hZ⟩ := check_t D V u T hp hv hc true
  exact replace_dial T h V p u l μ D hv hZ

def fields (G : Gauge) : Deck G :=
  Classical.choice (Deck.setting G)

def options (G : Gauge) : LitBook (fields G) :=
  Classical.choice (Menus.existence _)

def opened (G : Gauge) : Booked (fields G) :=
  Classical.choice (Land.suitable _)

def columns (G : Gauge) : MS_Data G (opened G) :=
  Classical.choice (Land.bookedMS _)

theorem removes_precise_marks (Z : Run) (hG : G.Simple) :
    let M := opened G;
    let S := columns G;
    let V := options G
    ∃ Q : Prescription (fields G),
      TaylorOK S V Q ∧
        ∀ (W : Type) (_ : LinearOrder W) (_ : Fintype W) (X : W → QP) (u : W → Label (fields G))
          (μ : ℝ),
          Injective X →
            ∃ d : ℕ,
              let Y := shot Z d X μ;
              let h : safe Y := shot_large Z d X μ;
              let F := tally Y h V Q u;
              Dial.Uses Y atTop μ ∧
                coherent M S V u Y μ true Q atTop F ∧
                  (∀ s n,
                    Tendsto (fare (Label.h ∘ u) Y.profile (PeakT.ordZ F) s n) atTop
                      (𝓝 (tour S u μ X s n))) := by
  intro M S V
  obtain ⟨A, hA, h⟩ := applied_Dial V S hG
  refine ⟨A, hA, fun W _ _ x u μ hx => ?_⟩
  obtain ⟨d, hv⟩ := usable Z x hx μ
  let P := shot Z d x μ
  have he := h _ _ inferInstance P atTop μ u (shot_large Z d x μ) hv
  exact ⟨d, hv, he, fun s n => (Dial.profile_t S V u P he hv hx (photographed Z d x μ) s n).2⟩
end YM.WilsonMS.Removed
