import YM.Integration.WilsonReportingPrescribedOldMicroscopic
import YM.RGComparison.Core16.Insertions

/-! The independently issued MS film is a finite sum of actual nonlinear UV Wilson
measurements on the original positions and underlying field. Its whole earlier reading
uses the submitted masked source, earlier Gibbs denominator and the original cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichOriginalPortfolio
open Function MeasureTheory Lattice Wilson RG Source Marker Precision
open IterationFour.Vacuum LocalComparison PhysicalNext.Repeat.Legato
open Push.GridApprox MergeProof MergeProof.Accent
open RG3.Script.Picnic FullQLocal.RenderedStep RGComparison.Core16
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical
open scoped Classical BigOperators
variable {G:Gauge}{B:Deck G}(R:Run G)

def label (N p:ℕ){h:ℕ}(a:Glyph B h):R.family.label a.size:=
  Descent.fieldLabel R.family N p (ActualOriginalDictionary.coordinates R B a.size a.grade a.2.2)

def observation (Q:Prescription B)(N p:ℕ)(v:Label B)(μ:ℝ)(k:ℕ)
    (x:Site (R.family.side N p))(U:Config G (R.family.side N p)):ℂ:=
  ∑a:Glyph B v.h,oil (Q.fees v.h v.item) a k μ*R.family.O N p (label R N p a) x U

theorem observed (Q:Prescription B)(N p:ℕ)(v:Label B)(μ:ℝ)(k:ℕ)
    (x:Site (R.family.side N p))(U:Config G (R.family.side N p)):
    ActualOriginalCalibratedColumns.weightedObservable R B Q v μ (R.family.side N p) x U k=
      observation R Q N p v μ k x U:=by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  unfold observation label
  apply Finset.sum_congr _ ?_
  · ext a
    simp only [Finset.mem_univ]
  intro a _
  rw [Descent.field_label_correct]

variable {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (Q:Prescription B) {m per n:ℕ}
    {hm:n ≤ m + 1}(D:ActualRunQlocalNativeTuple.Datum R per (m + 1) n hm V)
    (u:V→Label B)(μ:ℝ)(orders:V→ℕ)(x:TestSpace (ActualRunQlocalNativeTuple.orbit D))

def roster (s:(Stock.census V).Mode)(U:Config G (R.family.side (m + 1) per)):ℂ:=
  ∏i∈s.val,ActualRunQlocalNativeTuple.reader D i (x i)*
    observation R Q (m + 1) per (u i) μ (orders i) (ActualRunQlocalNativeTuple.root D i) U

omit [Nonempty V] in
theorem corrected (s:(Stock.census V).Mode):
    ActualStartupNormalizedQ.modeObservable Q D u μ orders x s=roster R Q D u μ orders x s:=by
  funext U
  unfold ActualStartupNormalizedQ.modeObservable roster
  apply Finset.prod_congr rfl
  intro i _
  rw [observed]

include D in
theorem measured (simple:G.Simple)(age:∀a:ActualOriginalQReaders.Slot u,R.family.ref a.2.size ≤ m + 1)
    (j:ℕ)(live:j ≤ m + 1)(s:(Stock.census V).Mode)(U:Config G (R.family.side j per)):
    (((R.family.path.rep (m + 1) per j).eval U)⁻¹ • gust R.family.path (m + 1) per (m + 1)
      ((ActualOriginalQInput.input Q D u μ orders simple (m + 1) (le_refl _)).leaf x).density j live U).part s =
      actualTransport R.family (N:=m + 1) (roster R Q D u μ orders x s) live U:=by
  rw [←corrected]
  exact WilsonReportingPrescribedOldMicroscopic.original R Q D u μ orders simple (le_refl _) age x live s U

end YM.Integration.WilsonMacroscopicRichOriginalPortfolio
