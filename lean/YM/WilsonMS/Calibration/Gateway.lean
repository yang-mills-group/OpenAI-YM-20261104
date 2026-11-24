import YM.WilsonMS.Calibration.MarkedLPT
/-!
# The original binding and the compensated readings

`fullRead`: `expectation` in the φ-shifted coupling (WITH covariance on
the actual gauge quotient). Its inserted `markArray` are Taylor-polynomial
lifts of the same `Initialize` that went to the Wilson position scheme,
mixed by the `fees` (will be expressed as a matrix on fields by `FrameD`).
Exact `sum_read` on this prescription with `PhysicalSum`.

`pure_adapted` and `pure_parse`: original (non-Wick-compensated) reading
with the same survey's pre-compensation parts. Useful for customers in the
`LitBook`/`Tide.remove`/`Dial.LPT_to_MS` interface. This is where their
calls live; we *extend* those suppliers for the rest of the W-compensated
inputs, rather than applying their `TaylorOK` off-policy.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open Function Filter Set Finset MeasureTheory XSpace
open Lattice Maxwell Source Maxwell.Free Wilson
open MS MS.Plane MS.High MS.Native MS.Native.Wilsonian MS.Native.Studio
open MS.Menus MS.Local.Physical MS.Land MS.Book MS.Book.Convolve MS.Book.Program
open Cylinder Lab MS.Koszul MS.Lifting MS.Theater Tone Landau.Detect
open MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.SplitP MS.Puff.Mom Swirl Swirl.Near Fleet
open Rescaled Webs Corrected Rake Tide Vane Orbit Dial Osc
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (V : XSpace.Initialize G) (x : ℝ) {c t : XSpace.Period} {d : ℕ}
local notation "B" => Ensure.deck G
variable {W I : Type}
section direct
variable (P : Period) (T : P.Tree) (A : Cover) (a : Prescription (Ensure.deck G)) (C : W → Cover)
  (u : W → Label (Ensure.deck G))

def fullRead (s : Finset W) :=
  expectation T G a.team x (∏ i ∈ s, markArray V a.team x P T (A + C i) (a.fees (u i).h (u i).item))
variable [LinearOrder W]

theorem sum_read (s : Finset W) :
    PhysicalSum G a.team x P.side true s C A (fieldSeries V (Stripped a.team) a u)
      (Coupling.read (fullRead V x P T A a C u s)) :=
  finite_top T G a.team x _ A C _ (fun i => aligned V a.team x P T A (C i) _) s

/-- Original LitBook connection. Uses SAME uncorrected parts of the XSpace columns. -/
def pureColumn (S : Acts B d) (i : W) :=
  ∑ g : Glyph B d,
    XSpace.Bare.scalar T (wavesP S x g) *
      Coupling.composeS (Program.shift a.team x)
        (Bare.raw T (V.surveys g.size) (wrap P.side (A + C i)) (Theater.ΕData B g))
local notation "Φ" => Webs.Midpt.portfolio V

omit [LinearOrder W] in
lemma pure_pairs (S : Acts B d) (i : W) :
    Correspond T G a.team x (promote (Mark_T G P.side A (C i)) (Menus.rent Φ (Stripped a.team) S x))
      (pureColumn V x P T A a C S i) := by
  have h :
    promote (Mark_T G P.side A (C i)) (Menus.rent Φ (Stripped a.team) S x) =
      ∑ g : Glyph B d,
        Rescaled.priced (wavesP S x g)
          (promote (Mark_T G P.side A (C i)) (Glyph.preamble Φ (Stripped a.team) g x)) := by
    ext1 n
    rw [promised, Menus.rent, map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    unfold Rescaled.priced
    rw [map_sum, paired]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul]
    simp only [LinearMap.lsmul_apply, promised, wavesP, Coupling.read, PowerSeries.coeff_mk]
  rw [h]
  exact
    Correspond.sum _ fun j _ =>
      Correspond.scale _ (received_pair a.team x _ T _ _ (Theater.filmBasic B j))

def plainRead (s : Finset W) :=
  expectation T G a.team x (∏ i ∈ s, pureColumn V x P T A a C (a.fees (u i).h (u i).item) i)

lemma pure_adapted (s : Finset W) :
    PhysicalSum G a.team x P.side true s C A (ApplyM Φ (Stripped a.team) a u)
      (Coupling.read (plainRead V x P T A a C u s)) :=
  finite_top T G a.team x _ A C _ (fun _ => pure_pairs ..) s
end direct
section budget
variable [LinearOrder W]
variable (p : Trial I W) (h : Removed.safe p) (A : Prescription (Ensure.deck G))
  (u : W → Label (Ensure.deck G))

def islandV (n : I) :=
  Schedule.island p.side n (h n)

def uncut (n : I) (s : Finset W) :=
  Coupling.read
    (fullRead V (p.profile.η n) (islandV p h n) (V.tree _) (p.head n) A (fun i => p.off i n) u s)
local notation "Z" => uncut V p h A u

omit [LinearOrder W] in
lemma starts_full (i : I) : Z i ∅ = Trunk.unit := by
  unfold uncut fullRead
  rw [Finset.prod_empty, Removed.expects_one]
  funext n
  change PowerSeries.coeff n 1 = SplitP.refineV useN (1 : ℂ) n
  rw [PowerSeries.coeff_one, SplitP.refineV]
  split_ifs with he hh ht <;>
    first
    | rfl
    | exact (hh he).elim
    | exact (he ht).elim

def tagD : Terrify W I := fun s i n => Puff.Log.Meter Trunk (SplitP.marked W) (Z n) s i

lemma logs_out (n : I) (s : Finset W) : bury n s (tagD V p h A u) = Z n s :=
  congr_fun
    (Puff.Log.solve Trunk (SplitP.marked W) (Z n) (starts_full V p h A u n)
      (fun _ _ _ => Submodule.mem_top))
    s

lemma on_m (n : I) (s : Finset W) :
    PhysicalSum G A.team (p.profile.η n) (dimT p.side n) true s (fun i => p.off i n) (p.head n)
      (fieldSeries V (Stripped A.team) A u) (bury n s (tagD V p h A u)) := by
  rw [logs_out]
  exact sum_read V (p.profile.η n) (islandV p h n) (V.tree _) _ A (fun i => p.off i n) u s

lemma empty : tagD V p h A u ∅ = 0 := by
  funext n i
  exact congr_fun (Puff.Log.happy Trunk (SplitP.marked W) (Z i)) n
variable {S : Rake.Label B} {M : Booked (Ensure.deck G)} (F : MS_Data G M) (μ : ℝ)
local notation "Q" => tagD V p h A u

theorem adjusted (hc : G.Simple) (hv : Installed V F A) (l : Filter I) (hw : Dial.Uses p l μ) :
    ∃ X,
      CCOrb G p.profile.η A.team p.head p.side (goalsK p.off p.profile.η (PortFull V A ∘ u)) true X ∧
        (∀ a : ℝ, ∀ s n, Tide.PeakT l p.profile a (Q s n - X s n)) ∧
          (∀ s n,
            PeakT.twin l p.profile mildG (fare (Label.h ∘ u) p.profile Q s n)
                (fun i => book F u μ (testP p i) s n) ∧
              PeakT.twin l p.profile mildG (fare (Label.h ∘ u) p.profile (PeakT.ordZ Q) s n)
                (fun i => tour F u μ (testP p i) s n)) := by
  obtain ⟨t, hT, hB⟩ := Tide.qualifies p.off hw.total hw.reality hw.upright hw.super
  obtain ⟨Z', X, Y, ⟨he, he', hx, hc'⟩, hz, hF, H, hX, hH⟩ :=
    phase_read u p.off hc hv hw.clear hw.wind hT hw.knit hB true
  have hC : Z' = Q := by
    let P (v : Terrify W I) i s n := v s n i
    funext s n i
    have hL (V : Terrify W I) (hV : V ∅ = 0) :
      Puff.Log.Meter Trunk (marked W) (fun s => bury i s V) = P V i :=
      Puff.Log.recheck _ _ _ (show P V i ∈ allIndex _ _ from fun _ _ _ _ => Submodule.mem_top)
        (Tide.pointed _ hV i)
    have hz' : (fun s => bury i s Z') = fun s => bury i s Q :=
      funext fun t => classicalμ (τ_nil ..) (hc' i t) (on_m ..)
    obtain hp := hL Z' he
    rw [hz', hL _ (empty ..)] at hp
    exact Eq.symm (congr_fun (congr_fun hp s) n)
  have hv (t n) : Fleet.toZ Y t n = (fun i => book F u μ (testP p i) t n) :=
    funext fun i => Point_t F u μ (posed (μ := μ) p.off hw.knit) hz i t n
  subst Z'
  refine ⟨X, hX, hH, fun s n => ?_⟩
  rw [← hv, ←
    show PeakT.ordZ (Fleet.toZ Y) s n = (fun x => tour F u μ (testP p x) s n) from
      funext fun i => shape_f F u μ (posed (μ := μ) p.off hw.knit) hz i s n]
  exact H s n

lemma pure_parse (i : I) (s : Finset W) :
    bury i s (Removed.tally p h (Webs.Midpt.portfolio V) A u) =
      Coupling.read
        (plainRead V (p.profile.η i) (islandV p h i) (V.tree _) (p.head i) A (fun k => p.off k i) u
          s) :=
  classicalμ (τ_nil ..) (Removed.tally_cut p h (Webs.Midpt.portfolio V) A u i s)
    (pure_adapted V (p.profile.η i) (islandV p h i) (V.tree _) _ A (fun k => p.off k i) u s)
end budget
end YM.WilsonMS.BMenu
