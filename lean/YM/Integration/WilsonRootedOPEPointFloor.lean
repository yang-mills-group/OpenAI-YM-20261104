import YM.Integration.WilsonRootedOPEGlyph
import YM.Integration.WilsonRootedTwoDateOldPhase

/-! The exact previous normalized point reader pays every original signed fee on an actually nonzero calibration row before the period and the ultraviolet cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointFloor
open Filter Function Finset Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges
open FullQLocal Push.PriceCompiler PhysicalNext.JointLoad
open scoped BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (u : V→MS.Rake.Label B) {p L : ℕ} (o : V→Site (R.family.side L p)) (a b : V→ℕ)
local notation "D₀" => ActualOriginalQPointDatum.datum R p L o a b
local notation "oneW" => fun _ : V=>(1:ℝ)

omit [DecidableEq V] [Fintype V] in
theorem unit (i : V) : 1≤readerPrice (D₀) i := by
  let D := ActualRunQlocalNativeTuple.orbit (D₀)
  let x := WilsonOriginalPointModes.unit D
  have native := native_reader_bound (D₀) i x
  have actual : ActualRunQlocalNativeTuple.reader (D₀) i (testInclusion D x i)=(testInclusion D x i).val 0 := ActualOriginalQPointDatum.reader_eq R p L o a b i _
  rw [actual,WilsonOriginalPointModes.unit_read D i,norm_one] at native
  exact native

theorem floor {width : ℝ} (hw : 0≤width) (z : Row (R:=R) u) :
    WilsonRootedOPEGlyph.mass R u z≤rowPrice (D₀) u (oneW) width z := by
  have base := WilsonRootedOPEGlyph.mass_nonneg R u z
  have rooted := unit R o a b z.1.1
  have rising : 1≤Real.exp (width*(rowFall u z:ℝ)) := Real.one_le_exp (mul_nonneg hw (Nat.cast_nonneg _))
  have reorder : rowMass (D₀) u z=WilsonRootedOPEGlyph.mass R u z*readerPrice (D₀) z.1.1 := by unfold rowMass WilsonRootedOPEGlyph.mass;ring
  rw [rowPrice,reorder,show Poly.toll (oneW) ((Stock.census V).fire z.1.1) = 1 by simp [Poly.toll],one_mul]
  exact (le_mul_of_one_le_right base rooted).trans (le_mul_of_one_le_right (mul_nonneg base (zero_le_one.trans rooted)) rising)

theorem funded (Q : MS.Land.Prescription B) (μ : ℝ) (orders : V→ℕ) {width : ℝ} (hw : 0≤width) (N : ℕ) (s : Slot u) :
    ‖fee Q u (μ-R.family.S.scale N) orders s‖ / ActualOriginalQNormalization.normalizer Q (D₀) u μ orders N (oneW) width ≤
    (WilsonRootedOPEGlyph.mass R u (WilsonRootedOPEGlyph.row R u s))⁻¹ := by
  let z := WilsonRootedOPEGlyph.row R u s
  let c := ActualOriginalQNormalization.normalizer Q (D₀) u μ orders N (oneW) width
  let w := fun i : Slot u=>‖fee Q u (μ-R.family.S.scale N) orders i‖
  let pay := fun t : Row (R:=R) u=>w t.1*rowPrice (D₀) u (oneW) width t
  have parent := (WilsonRootedOPEGlyph.acquired R u s).1
  have active : 0<WilsonRootedOPEGlyph.mass R u z := (WilsonRootedOPEGlyph.acquired R u s).2
  have positive : 0<c := zero_lt_one.trans_le (le_max_left _ _)
  have nonneg (t : Row (R:=R) u) : 0≤pay t := mul_nonneg (norm_nonneg _) (row_price_nonneg (D₀) u (oneW) width (fun _=>zero_lt_one) t)
  have inside : pay z≤c := (Finset.single_le_sum (fun i (_:i∈Finset.univ)=>nonneg i) (Finset.mem_univ z)).trans (le_max_right _ _)
  have bill : w s*WilsonRootedOPEGlyph.mass R u z≤c := by
    have grown : w z.1*WilsonRootedOPEGlyph.mass R u z≤c := (mul_le_mul_of_nonneg_left (floor R u o a b hw z) (norm_nonneg (fee Q u (μ-R.family.S.scale N) orders z.1))).trans inside
    change w z.1*WilsonRootedOPEGlyph.mass R u z≤c at grown
    rw [show z.1=s from parent] at grown
    exact grown
  change w s/c≤(WilsonRootedOPEGlyph.mass R u z)⁻¹
  calc
    _ ≤ (c/WilsonRootedOPEGlyph.mass R u z)/c := div_le_div_of_nonneg_right ((le_div_iff₀ active).mpr bill) positive.le
    _ = _ := by field_simp

end YM.Integration.WilsonRootedOPEPointFloor
