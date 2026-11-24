import YM.FormalOPE.RG10.FiniteTop
import YM.PertExtension.BareWords

/-!
# Stamp actual `SectionData` basis in the WilsonX regulator ledger

Use the **same** `C : Family G`. We use `Next.Foundations` valued-stencil data
(import consumer `Floral` proof separately). Need actual and formal snapshots still matched in
later couplings/histories/estimates; do not assume equality from being parameterized by C --
`Orb` is a distinct regulator. Keep track of the original field horizon on *every* insertion.
The included labels are in pre-quotient reference frames. Thus making a new stencil with
`C.localSection d'` at a larger horizon d' for an existing field is **not justified**; even a
proof the same abstract continuum label obtained by `raiseLabel` is not such an assertion. The
compatible pre-quotient coefficient family here uses finite-horizon lists of these **original**
stamp encodings (and retain summation/mixing coefficients of those stamps). For the stated pivot
convention choose each to include the tuning & top re-expression of its own-horizon input field;
the FieldSystem/pivot/tuning supplies are explicit missing obligations. Additional operators e.g.
unit test derivatives, measure/J/EOM insertions may be kept on stamps outside this cylinder list
in `combine_at`; no Gram projections done here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionTop
open Gauge Lattice PertExtension PertExtension.Chart PertExtension.Orb PertExtension.Orb.SlotEvaluation
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open Precision PowerSeries MeasureTheory Filter Function Source RG Labels Marker Extra.Trajectories
open scoped ContDiff Topology BigOperators Classical

variable {G : Gauge} {n : Side} (hn : Even n.val)
local notation "P" => tray G
local notation "F" => feed (G:=G) hn
local notation "W" => vertices G n
variable {d : ℕ} {R : Labels.Frame G d} {S : Source.SectionData R} {H : Hol G}

namespace Stamp

/-- From a lift expressed in the active section, before any Wick/frame transforms. -/
def native (o : Site n) (s : S.Sound H) (p : Bid.pop S) (i : R.Index) : Stamp G n where
  stencil := fieldAt S i o
  slots := (R.grades i).2
  test := (pre_field S s p i o).1
  cleared k hk := by
    obtain ⟨h,h'⟩ := pre_field S s p i o
    funext x; unfold raw
    rw [row_lift, jets_vanish h.curved.germ h' hk]; rfl

lemma nativeUnit (o : Site n) (s : S.Sound H) (p : Bid.pop S) :
    (native o s p 0).couplingMark = 1 := by
  let A := native o s p 0
  have he : Uses.AtCoupling (1 : Wilson.Config G n → ℝ) 0 (1 : Kernel (Unit × Dir G n)) := by
    unfold Uses.AtCoupling; rw [delay_zero]; exact raw_one.symm
  have hu : A.slots = 0 := congr_arg Prod.snd R.zero_degree
  have hx : A.stencil = 1 := by ext; exact congr_fun (@SlotEvaluation.unit_zero G n d R S H s o) _
  change A.couplingMark = _; apply delay_inj A.slots
  rw [A.atCoupling, hx, hu, he]

section field

variable (C : Family G)
/-- Pre-quotient access, using original field-horizon per insertion. Payload
of a test with addressed derivatives is not being projected away; include derivatives as scalars
with these labels or as linear combinations, NOT as an equality of horizon frames. -/
structure Reservation (C : Family G) (n : Side) (d : ℕ) where
  height : ℕ
  admitted : height ≤ d
  leg : (C.labels.level height).Index
  anchor : Site n

def admitHigher {C : Family G} (x : Reservation C n d) {k : ℕ} (h : d ≤ k) : Reservation C n k :=
  { x with admitted := x.admitted.trans h }

variable (hC : C.Makes) (p : ∀ d, Bid.pop (C.localSection d)) (x : Reservation C n d)

def placed := native x.anchor (hC.sections _) (p x.height) x.leg

lemma higherSame {k} (h : d ≤ k) : placed C hC p (admitHigher x h) = placed C hC p x := rfl

/-- `Stamp.stencil` is literally a `places` on the same Family as the Wilson comparison, on all
these (pre-reprice) labels. The code also reprices on physical tori. -/
theorem named (u : Wilson.Config G n) :
    ↑((placed C hC p x).stencil u) =
      (C.localSection x.height).places (Pi.single x.leg 1) x.anchor u := scalar_real (hC.sections _) ..

theorem before_offset (N q : ℕ) (x : Reservation C (C.side N q) d) (u : Wilson.Config G (C.side N q)) :
    ((placed C hC p x).stencil u : ℂ) =
      C.O N q (SameColumns.reprice C N q (d:=x.height) (Pi.single x.leg 1)) x.anchor u := by
  rw [SameColumns.reprice_eq]; exact named C hC p x u

variable {I : Type} [Fintype I] [DecidableEq I] {U : Type} [DecidableEq U] [Fintype U]
    {A : Census I} {B : Census U} (x : I → Reservation C n d)

def program (A : Census I) := (F).contraction W (publish A (placed C hC p ∘ x))

/-- Common all-positive-order ledger before position/Wick frame normalization. -/
theorem common_top : (F).markedFunded W (publish A (placed C hC p ∘ x)) ∧
    Word.vac A (program hn C hC p x A) = 0 ∧
    Word.expMark (program hn C hC p x A) = Word.package (R:=A) fun s =>
      lower (degrees (placed C hC p ∘ x) s.val)
        (into (PowerSeries.mk (diag (restrictedO (shafts (placed C hC p ∘ x) s.val))))) := by
  obtain ⟨ho,hu,ht⟩:= markedOrbit hn A (placed C hC p ∘ x)
  exact ⟨ho,hu,ht.trans (ordinaryOrbit ..)⟩

omit [Fintype I] [DecidableEq I] in
lemma taller {k} (h : d ≤ k) (i : I) :
    (placed C hC p ∘ (fun i => admitHigher (x i) h)) i = (placed C hC p ∘ x) i := rfl

/-- The same field-horizon reservation is coherent in any order comparison with the same data. -/
theorem accommodates {k} (h : d ≤ k) (x' : U → Reservation C n k) (u : Names A B)
    (he : ∀ i, admitHigher (x i) h = x' (u.e i)) (r : ℕ) :
    let c := program hn C hC p x A
    let c' := program hn C hC p x' B
    PowerSeries.trunc (r+1) c = PowerSeries.trunc (r+1) (Word.eraseMarks u c') ∧
      PowerSeries.trunc (r+1) (Word.expMark c) = PowerSeries.trunc (r+1) (Word.eraseMarks u (Word.expMark c')) := by
  have hk : placed C hC p ∘ x = fun i => placed C hC p (x' (u.e i)) := funext (fun i => by rw [← he i]; rfl)
  dsimp only [program]; rw [hk]; exact existing_subset hn B (placed C hC p ∘ x') r A u
end field
end Stamp
end YM.FormalOPE.RG10.InversionTop
