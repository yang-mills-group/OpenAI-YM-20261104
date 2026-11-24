import YM.Integration.ActualOriginalQPackets
import YM.Integration.NativeFinitePacketExactCost
import YM.Integration.ActualOriginalFeeGrowth

/-! Exact cancellation in the literal full-Q packet's payment formula.
The regulator power and the original Frame threshold power cancel, leaving
the full fee coefficient times the original finite field/path price. Neither
the remaining price nor its period dependence is suppressed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQCharges

open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM
open ActualOriginalQReaders ActualOriginalQPackets
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B)

def tensorMass (s : Row (R := R) u) : ℝ :=
  ∑ j : Fin (ActualRunKernelPackets.tokenRank R (degree u) s) → G.ColorIndex,
    ‖NativeCurvatureTensor.coefficient
      (fun k => (NativeCurvatureTensor.word s.2.2.val k).2) j‖

def rowMass (s : Row (R := R) u) : ℝ :=
  tensorMass u s *
    ‖MvPolynomial.coeff s.2.2.val
      ((ActualRunCurvaturePackets.ofRun R (degree u s.1)).data.shape s.2.1)‖ *
    readerPrice D s.1.1 * ‖coordinates (R := R) u s.1 s.2.1‖

def rowFall (s : Row (R := R) u) : ℕ :=
  (⟨fun k => (ActualRunCurvaturePackets.ofRun R (degree u s.1)).data.columns
      s.2.1 (NativeCurvatureTensor.word s.2.2.val k).1, fun _ => 0⟩ :
    Atom G (ActualRunKernelPackets.tokenRank R (degree u) s)).length

def rowPrice (w : V → ℝ) (width : ℝ) (s : Row (R := R) u) : ℝ :=
  Poly.toll w ((Stock.census V).fire s.1.1) * rowMass D u s *
    Real.exp (width * rowFall u s)

def totalRowPrice (w : V → ℝ) (width : ℝ) : ℝ :=
  ∑ s : Row (R := R) u, rowPrice D u w width s

omit [DecidableEq V] [Fintype V] in
private theorem reader_price_nonneg (i : V) : 0 ≤ readerPrice D i := by
  let x : IndependentTests (ActualRunQlocalNativeTuple.orbit D) := fun j =>
    ⟨0, (Orbit.Bill.zero (U := ActualRunQlocalNativeTuple.orbit D j)).more zero_le_one⟩
  exact (norm_nonneg _).trans (native_reader_bound D i x)

omit [DecidableEq V] [Fintype V] in
private theorem row_mass_nonneg (s : Row (R := R) u) : 0 ≤ rowMass D u s := by
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _))
      (reader_price_nonneg D s.1.1)) (norm_nonneg _)

theorem row_price_nonneg (w : V → ℝ) (width : ℝ) (hw : ∀ i, 0 < w i)
    (s : Row (R := R) u) : 0 ≤ rowPrice D u w width s := by
  exact mul_nonneg
    (mul_nonneg (Poly.worth hw ((Stock.census V).fire s.1.1)).le
      (row_mass_nonneg D u s)) (Real.exp_pos _).le

private theorem cancel_norms (z a b : ℂ) (t : ℝ) (r : ℕ)
    (hz : z ≠ 0) (ht : t ≠ 0) :
    ‖z ^ (-(r : ℤ))‖ * ‖z ^ r * (((t⁻¹ ^ r : ℝ) : ℂ) * a)‖ *
        ‖((t ^ r : ℝ) : ℂ) * b‖ = ‖a‖ * ‖b‖ := by
  have hz' : z ^ (-(r : ℤ)) * z ^ r = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hz)]
  have ht' : ((t⁻¹ ^ r : ℝ) : ℂ) * ((t ^ r : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow, inv_mul_cancel₀ ht, one_pow,
      Complex.ofReal_one]
  have he : z ^ (-(r : ℤ)) * (z ^ r * (((t⁻¹ ^ r : ℝ) : ℂ) * a)) *
      (((t ^ r : ℝ) : ℂ) * b) = a * b := by
    calc
      _ = (z ^ (-(r : ℤ)) * z ^ r) *
          (((t⁻¹ ^ r : ℝ) : ℂ) * ((t ^ r : ℝ) : ℂ)) * (a * b) := by ring
      _ = _ := by rw [hz', ht', one_mul, one_mul]
  rw [← norm_mul, ← norm_mul, he, norm_mul]

variable (Q : MS.Land.Prescription B) (μ : ℝ) (orders : V → ℕ)

/-- Both normalization powers cancel in each literal charged token. The
remaining row price is independent of the outer cutoff and of the tests. -/
theorem token_charge (N : ℕ) (hL : L ≤ N) (w : V → ℝ) (width : ℝ)
    (s : Row (R := R) u) :
    Poly.toll w ((Stock.census V).fire s.1.1) *
        ‖(Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
          (-(ActualRunKernelPackets.fieldRank R (degree u) s : ℤ))‖ *
        (token Q D u μ orders N s).coin *
        Real.exp (width * (token Q D u μ orders N s).fall) =
      ‖fee Q u μ orders s.1‖ * rowPrice D u w width s := by
  let z : ℂ := Pert.Asymptotics.regulatorRun R.family N p L
  let t : ℝ := (R.family.path.rep N p L).p.threshold
  let r : ℕ := ActualRunKernelPackets.fieldRank R (degree u) s
  let a : ℂ := MvPolynomial.coeff s.2.2.val
    ((ActualRunCurvaturePackets.ofRun R (degree u s.1)).data.shape s.2.1)
  let b : ℂ := coordinates (R := R) u s.1 s.2.1
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ActualRunKernelPackets.regulator_pos R N p L hL).ne'
  have ht : t ≠ 0 := (R.family.path.rep N p L).p.threshold_pos.ne'
  have hc := cancel_norms z a b t r hz ht
  change Poly.toll w ((Stock.census V).fire s.1.1) * ‖z ^ (-(r : ℤ))‖ *
      (tensorMass u s *
        (‖z ^ r * (((t⁻¹ ^ r : ℝ) : ℂ) * a)‖ *
          ((‖fee Q u μ orders s.1‖ * readerPrice D s.1.1) *
            ‖((t ^ r : ℝ) : ℂ) * b‖))) * Real.exp (width * rowFall u s) =
    ‖fee Q u μ orders s.1‖ *
      (Poly.toll w ((Stock.census V).fire s.1.1) *
        (tensorMass u s * ‖a‖ * readerPrice D s.1.1 * ‖b‖) *
          Real.exp (width * rowFall u s))
  calc
    _ = ‖fee Q u μ orders s.1‖ *
        (Poly.toll w ((Stock.census V).fire s.1.1) *
          (tensorMass u s *
            (‖z ^ (-(r : ℤ))‖ * ‖z ^ r * (((t⁻¹ ^ r : ℝ) : ℂ) * a)‖ *
              ‖((t ^ r : ℝ) : ℂ) * b‖) * readerPrice D s.1.1) *
                Real.exp (width * rowFall u s)) := by ring
    _ = _ := by rw [hc]; ring

/-- Exact finite cost of the existing packet, counting each original row once. -/
theorem packet_cost (N : ℕ) (hL : L ≤ N) (w : V → ℝ) (width : ℝ) :
    packetCost Q D u μ orders N w width =
      ∑ s : Row (R := R) u, ‖fee Q u μ orders s.1‖ * rowPrice D u w width s := by
  unfold packetCost packets packetCount
  rw [NativeFinitePacketPayment.totalCost_ofFin]
  apply Fintype.sum_equiv (Fintype.equivFin (Row (R := R) u)).symm
  intro k
  exact token_charge D u Q μ orders N hL w width _

/-- A genuine cutoff-uniform polynomial majorant of the actual Paid cost.
The original finite geometry/test-reader price stays explicit; it is not
asserted to be period-uniform or below an admitted qlocal price. -/
theorem packet_cost_clock_bound (K : ℕ) (w : V → ℝ) (width : ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ (N : ℕ), L ≤ N →
      ∀ orders : V → ℕ, (∀ i, orders i ≤ K) →
        packetCost Q D u (μ - R.family.S.scale N) orders N w width ≤
          (C * (1 + ‖R.family.S.scale N‖) ^ d) * totalRowPrice D u w width := by
  obtain ⟨C, hC, d, h⟩ := ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  refine ⟨C, hC, d, ?_⟩
  intro N hN k hk
  rw [packet_cost D u Q (μ - R.family.S.scale N) k N hN w width]
  calc
    ∑ s : Row (R := R) u, ‖fee Q u (μ - R.family.S.scale N) k s.1‖ *
        rowPrice D u w width s ≤
        ∑ s : Row (R := R) u, (C * (1 + ‖R.family.S.scale N‖) ^ d) *
          rowPrice D u w width s := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_right
        (h s.1.1 (k s.1.1) (hk s.1.1) s.1.2 (R.family.S.scale N))
        (row_price_nonneg D u w width hw s)
    _ = (C * (1 + ‖R.family.S.scale N‖) ^ d) * totalRowPrice D u w width := by
      rw [totalRowPrice, Finset.mul_sum]

end YM.Integration.ActualOriginalQCharges
end
