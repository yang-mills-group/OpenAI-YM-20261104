import YM.Integration.WilsonReportingPrescribedOldGlyph
import YM.Integration.ActualOriginalQInput

/-! Independent old marked source on the reported Wilson family, including the true gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldSource

open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent MergeProof.Replicums RG3.Held RG3.Script.Picnic
open Extraction Table Spec RG17 MS MS.Menus MS.Local.Physical
open WilsonReportingPrescribedOldGrade WilsonReportingPrescribedOldGlyph
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : Layout F) {B : Deck G} (Q : MS.Land.Prescription B)

abbrev fee (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) (v : Glyph B u.h) : ℂ :=
  oil (Q.fees u.h u.item) v k μ

/-- The independently taxed signed source, written on the actual physical filed
column with all of its strictly lower Gaussian contractions removed. -/
def column (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) (r : ℝ) (N per : ℕ)
    (o : Site (R.family.side (L.level r) per)) (U : Config G (R.family.side (L.level r) per)) : ℂ :=
  let g := R.family.path.levels.clock.hatCoupling (L.level r)
  ∑ v : Glyph B u.h,
    ((scale R F L u.h r)⁻¹ *
      (((g^v.grade : ℝ) : ℂ) * observed R F L v r (fee Q u μ k v) N per o U) -
    fee Q u μ k v * (R.family.localSection v.size).places (lower R v g) o U)

theorem prescribed (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) (N per : ℕ)
    (age : ∀ v : Glyph B u.h, R.family.ref v.size ≤ L.level r) (future : L.level r ≤ N)
    (o : Site (R.family.side (L.level r) per)) (U : Config G (R.family.side (L.level r) per)) :
    ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side (L.level r) per) o U k =
      column R F L Q u μ k r N per o U := by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  unfold column
  apply Finset.sum_congr rfl
  intro v _
  rw [WilsonReportingPrescribedOldGlyph.original R F L v r (fee Q u μ k v) N per
    (age v) future o U]
  have hs : scale R F L u.h r ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (div_pos hr (R.family.S.a_pos _)).ne')
  change fee Q u μ k v * (R.family.localSection v.size).places (raw R v) o U = _
  field_simp [hs]
  ring

variable {n : ℕ} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- The original Q input and its entire old forced gas, in all marker modes,
are the Wilson birth of the corrected genuinely reported columns on every field. -/
theorem original (hG : G.Simple) (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
    (r : ℝ) (hr : 0 < r) (N per : ℕ) {hn : n ≤ L.level r}
    (D : ActualRunQlocalNativeTuple.Datum R per (L.level r) n hn V)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ L.level r)
    (future : L.level r ≤ N) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side (L.level r) per)) :
    ((ActualOriginalQInput.input Q D u μ orders hG N future).leaf x).density U =
      birth (Stock.census V) (R.family.path.rep N per (L.level r))
        (fun i W => ActualRunQlocalNativeTuple.reader D i (x i) *
          column R F L Q (u i) μ (orders i) r N per (ActualRunQlocalNativeTuple.root D i) W) U := by
  rw [ActualOriginalQInput.density_full Q D u μ orders hG N future age x U]
  congr 2
  funext i W
  rw [prescribed R F L Q (u i) μ (orders i) r hr N per (fun v => age ⟨i,v⟩) future]

end YM.Integration.WilsonReportingPrescribedOldSource
