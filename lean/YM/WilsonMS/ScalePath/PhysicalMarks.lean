import YM.WilsonMS.Top.Register
import YM.MS.Tide.Coi

/-!
# Exact body for LitBook stencils

Image the gauge reads (actual local germ at each period) with translations.
Thus no artificial cochains required from `Aura`; any Wilson dictionary
passing `Aura` gives the finite-top interpretation. This deals first with
literal `preamble`, without diagonal W-subtraction (you can also build a
larger mark with additions and finite frame shifts).
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Rescaled
open Root Coupling Quo Precision Lattice Function XSpace XSpace.Period
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.Native MS.Native.Wilsonian
  MS.Native.Chart MS.Native.Sew
open MS.Book MS.Book.Convolve MS.Book.Program MS.Plane MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Fleet
open MS.Swirl MS.Swirl.Near MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Engine MS.Puff.Mom
open MS.Menus MS.Local MS.Local.Physical MS.Tide MS.Native.Studio MS.Land
open scoped Topology ContDiff BigOperators

variable {P : Period} (T : P.Tree) (G : Gauge) (φ : Team) (x : ℝ)
local notation "N" => P.side
local notation "Σ'" => σbranch (G := G) (n := N)
local notation "Λ" => Master G N true
local notation "BS" => XSpace.Bare.Series T G
local notation "g'" => NRG (Stripped φ) x N G true

abbrev translateE (w : Site N) :=
  thread (fun i => w + i) id

def translateO (O : Obs (P := P) G) (w : Site N) : Obs (P := P) G := fun U => O (U ∘ translateE w)

lemma translate_read (w : Site N) (O : Obs (P := P) G) :
    in_chart G (translateO G O w) = (in_chart G O) ∘ Sew.pull (translateE w) :=
  rfl

lemma translate_gauge (O : Obs (P := P) G) (h : OpenGauge (drive N) O) (w : Site N) :
    OpenGauge (drive N) (translateO G O w) := by
  intro g U
  unfold translateO
  rw [show
      siteGauge (drive N) g U ∘ translateE w =
        siteGauge (drive N) (fun x => g (w + x)) (U ∘ translateE w)
      from ?_]
  apply h
  funext j
  simp [siteGauge, endRail, translateE, thread, add_assoc]
variable {F : Dot G Cover} {d : ℕ} (w : Cover) (O : Obs (P := P) G)
variable (h : enters P.side F = inscription G O) (hv : germ (in_chart G O))

include h hv in
lemma translate_body : enters N (Lab.Shift w F) = inscription G (translateO G O (Lattice.wrap N w)) := by
  have he : shown N F = Sew.art id (in_chart G O) := Subtype.ext (h.trans (Eq.symm (pooled id hv)))
  change (transport _ (Lab.Shift w F)).val = _
  rw [trans_shift F]
  rw [show transport _ F = shown N F from rfl, he]
  unfold Lab.Shift
  rw [map_sec, pooled _ hv]
  rfl

lemma from_moves (hf : From F.val d) : From (Lab.Shift w F).val d := by
  intro l hl
  let D := Lab.Shift w F
  let t : ℤ := l.length
  rw [← enough _ (F := D.val) (show (l.length : ℤ) = t from rfl), ← mask_s]
  have hx : model t D = 0 := by
    rw [show model t D = Lab.Shift w (model t F) from (mod_ferry ..).symm, show model t F = 0 from ?_,
      map_zero]
    apply Subtype.ext
    ext v
    by_cases hv : (v.length : ℤ) = t
    exact
      (enough v hv).trans
        (hf v
          (by
            unfold t at *
            omega))
    exact strange v hv
  rw [hx]
  rfl
variable {y : Cover}

include h hv in
lemma pays (hF : From F.val d) (hg : OpenGauge (drive N) O) :
    Offered G (translateO G O (Lattice.wrap N w)) d := by
  refine
    ⟨?_,
      ContDiffAt.comp (f := ⇑(Sew.pull (G := G) (translateE (P := P) (wrap N w)))) 0
        (by
          rw [map_zero]
          exact hv)
        (Sew.pull (G := G) (translateE (P := P) (wrap N w))).contDiff.contDiffAt,
      ?_⟩
  · rw [← translate_body G w O h hv]
    exact from_pass _ (from_moves G w hF)
  intro a _ z
  rw [show Lattice.gauge a z = siteGauge (drive N) (fun x => (a x)⁻¹) z from
      funext fun i => by simp [siteGauge, Lattice.gauge, Chart.drive, endRail]]
  apply translate_gauge _ _ hg

lemma translates (A c : Cover) {O : Obs (P := P) G}
    (h : enters N (Lab.Shift (A + c) F) = inscription G O) :
    promote (Mark_T G N A c) (substitute (shift φ x) (levels d F)) = fourierMark G φ x O d := by
  rw [Program.comm]
  unfold fourierMark
  refine congr_arg _ (funext fun i => ?_)
  rw [promised, promised, Position.mark_fourier]
  let k : ℤ := i + (d : ℤ)
  have he : Lab.Shift (A + c) (model k F) = model k (Lab.Shift (A + c) F) := mod_ferry ..
  change specialize _ (enters N (Lab.Shift (A + c) (model k F))) = _
  rw [he,
    show enters N (model k _) = mask k (enters N (Lab.Shift (A + c) F)) from
      enterShim (b := false) (h := Lab.Shift (A + c) F) N k,
    h]
  rfl

lemma translate_pair (A c : Cover) {O : Obs (P := P) G} (hf : Offered G O d)
    (h : enters N (Lab.Shift (A + c) F) = inscription G O) :
    Correspond T G φ x (promote (Mark_T G N A c) (substitute (shift φ x) (levels d F)))
      (litMark T G φ x O d) := by
  rw [translates G φ x A c h]
  exact Correspond.start _ _ hf

section lit
variable {G} {B : Deck G} (V : LitBook B)

/-- concrete copies at every periodic mesh. Here arbitrary choice of
unscaled Wilson stencil realization from LitBook (only germ matters).
Users may plug their actual stencil via equality of the germ. -/
def matrixO (k : Side) (u v : ℕ) (i : B.BIndex u v) :=
  ((V.levels u v i).pay k).choose

lemma matrix_reads (u v : ℕ) (i : B.BIndex u v) :
    enters N (V.stamp u v i) = inscription G (matrixO V N u v i) :=
  ((V.levels u v i).pay N).choose_spec.2.2

abbrev motionLit (i : Glyph B d) : Obs (P := P) G :=
  translateO G (matrixO V N _ _ i.2.2) (Lattice.wrap N w)

def native_entry (i : Glyph B d) :=
  litMark T G φ x (motionLit w V i) i.grade

lemma lit_pair (A c : Cover) (i : Glyph B d) :
    Correspond T G φ x (promote (Mark_T G N A c) (Glyph.preamble V (Stripped φ) i x))
      (native_entry T φ x (A + c) V i) := by
  have hf := ((V.levels i.size i.grade i.2.2).pay N).choose_spec
  unfold Glyph.preamble
  rw [strip_wobble]
  apply translate_pair
  exacts
    [pays G _ _ (matrix_reads V i.size i.grade i.2.2) hf.2.1 (V.levels i.size i.grade i.2.2).low hf.1,
    translate_body G _ _ (matrix_reads V i.size i.grade i.2.2) hf.2.1]

/-- The position-independent field matrix at a fixed regulator and scale x. -/
def wavesP (v : Acts B d) (x : ℝ) (i : Glyph B d) : Cn :=
  PowerSeries.mk (fun j => oil v i j x)

def columnP (v : Acts B d) :=
  ∑ i : Glyph B d, XSpace.Bare.scalar T (wavesP v x i) * native_entry T φ x w V i

lemma lit_rent (u : Acts B d) (A c : Cover) :
    Correspond T G φ x (promote (Mark_T G N A c) (Menus.rent V (Stripped φ) u x))
      (columnP T φ x (A + c) V u) := by
  let K := Mark_T G N A c
  let U (i : Glyph B d) := promote K (Glyph.preamble V (Stripped φ) i x)
  have hx :
    promote K (Menus.rent V (Stripped φ) u x) = ∑ i : Glyph B d, priced (wavesP u x i) (U i) := by
    ext1 n
    rw [promised, Menus.rent, map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    unfold priced
    rw [map_sum, paired]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    simp only [U, LinearMap.lsmul_apply, promised, wavesP, Coupling.read, PowerSeries.coeff_mk]
  rw [hx]
  exact Correspond.sum _ fun j _ => Correspond.scale _ (lit_pair T φ x V A c j)

open MS.Rake
variable {W : Type} (A c : Cover) (Q : Land.Prescription B) (i : Label B)

def from_book :=
  columnP T Q.team x (A + c) V (Q.fees i.h i.item)

variable (C : W → Cover) (u : W → Label B)

abbrev normalizedReading (s : Finset W) :=
  expectation T G Q.team x (∏ i ∈ s, from_book T x V A (C i) Q (u i))

variable [LinearOrder W]

theorem adapted (s : Finset W) :
    PhysicalSum G Q.team x P.side true s C A (ApplyM V (Stripped Q.team) Q u)
      (Coupling.read (normalizedReading T x V A Q C u s)) := by
  apply finite_top
  intro i
  exact lit_rent ..

theorem same_tree (L : P.Tree) (s : Finset W) :
    normalizedReading T x V A Q C u s = normalizedReading L x V A Q C u s := by
  have he := classicalμ (τ_nil ..) (adapted T x V A Q C u s) (adapted L x V A Q C u s)
  exact PowerSeries.ext fun i => congr_fun he i
end lit
end YM.WilsonMS.Rescaled
