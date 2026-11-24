import YM.Integration.WilsonRootedOPEPointNormalizer

/-! The point normalizer is one scalar on the entire original fine grid and
all periods at the same dates. Its full finite oil, tensor and path bill remains. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointCommon
open Function Finset Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
variable (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (orders:V→ℕ)

def scalar (N:ℕ) (width:ℝ) : ℝ := max 1 (∑z:Row (R:=R) u,
  ‖fee Q u (μ-R.family.S.scale N) orders z.1‖ *
    (WilsonRootedOPEGlyph.mass R u z * WilsonRootedOPEPointRows.reader * Real.exp (width*rowFall u z)))

omit [DecidableEq V] in
theorem positive (N:ℕ) (width:ℝ) : 1 ≤ scalar R Q u μ orders N width := le_max_left _ _

theorem original (J:Request V) (A:NumericSchedule R.family J) (d:LocalFormal.Datum R.family (Stock.census V))
    (o:V→Site (R.family.side (d.level+1) d.period)) :
    ActualOriginalQInitialInput.normalizer R simple u J A d Q o μ orders = scalar R Q u μ orders d.cutoff
      ((ActualOriginalQInitialInput.schedule R simple u J A).inputWidth d.level) := by
  let D:=ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let width:=(ActualOriginalQInitialInput.schedule R simple u J A).inputWidth d.level
  change max 1 (∑z:Row (R:=R) u,‖fee Q u (μ-R.family.S.scale d.cutoff) orders z.1‖*rowPrice D u (fun _=>1) width z)=_
  unfold scalar
  apply congrArg (max 1)
  apply sum_congr rfl
  intro z _
  apply congrArg (fun e:ℝ=>‖fee Q u (μ-R.family.S.scale d.cutoff) orders z.1‖*e)
  have reorder : rowMass D u z=WilsonRootedOPEGlyph.mass R u z * readerPrice D z.1.1 := by
    unfold rowMass WilsonRootedOPEGlyph.mass;ring
  rw [rowPrice,reorder,WilsonRootedOPEPointRows.point R J o,show Poly.toll (fun _:V=>1) ((Stock.census V).fire z.1.1)=1 by simp [Poly.toll],one_mul]

end YM.Integration.WilsonRootedOPEPointCommon
