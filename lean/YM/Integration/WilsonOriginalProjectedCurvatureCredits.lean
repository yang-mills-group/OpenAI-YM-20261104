import YM.Integration.WilsonOriginalProjectedCurvatureEnvelope

/-! At the registered period a single cutoff-independent original coefficient sum pays the complete
rooted offer on the positive registration records. Every root is assessed on
the same original geometric and colour data before selecting the cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureCredits
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ τ : ℝ) (extra : V → ℕ) (w : V → ℝ)

local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L
abbrev Funded := {i : Rows // 0 < wallet Q D u μ orders N i σ}

def quoted (i : Rows) : ℝ := (‖fee Q u μ orders i.1‖ *
    ActualOriginalQCharges.rowPrice D u w (σ+τ) i) * Real.exp (τ * (liftHeight D u i extra : ℝ))

def invoice : ℝ := ∑ i : Rows, quoted Q D u μ orders σ τ extra w i

theorem offered (hL : L≤N) (hg : 0<g₀) (hup : g₀≤1) (hw : ∀i,0<w i)
    (x : Site (R.family.side L p)) :
    SumBudget (fun i : Funded Q D u μ orders N σ =>
      if ActualRunQlocalNativeTuple.root D i.1.1.1 = x then
        Poly.toll w ((Stock.census V).fire i.1.1.1) * gross Q D u μ orders N i.1 σ τ extra
      else 0) (invoice Q D u μ orders σ τ extra w) := by
  let q := quoted Q D u μ orders σ τ extra w
  have qn (i : Rows) : 0≤q i := mul_nonneg
    (mul_nonneg (norm_nonneg _) (ActualOriginalQCharges.row_price_nonneg D u w _ hw i)) (Real.exp_pos _).le
  have gn (i : Funded Q D u μ orders N σ) : 0 ≤ gross Q D u μ orders N i.1 σ τ extra :=
    mul_nonneg i.2.le (Real.exp_pos _).le
  refine ⟨fun i => ?_,(hasSum_fintype _).summable,?_⟩
  · change 0 ≤ if ActualRunQlocalNativeTuple.root D i.1.1.1=x then Poly.toll w ((Stock.census V).fire i.1.1.1) * gross Q D u μ orders N i.1 σ τ extra else 0
    split <;> first | exact mul_nonneg (Poly.worth hw _).le (gn i) | exact le_rfl
  · refine (Summable.tsum_le_tsum (g:=fun i : Funded Q D u μ orders N σ => q i.1)
      (fun i => ?_) ((hasSum_fintype _).summable) ((hasSum_fintype _).summable)).trans ?_
    · split
      · have power : 1 ≤ ‖(g₀ : ℂ)^((grade u i.1 : ℤ) -
            (ActualRunKernelPackets.tokenRank R (degree u) i.1 : ℤ))‖ := by
          rw [phase, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg, zpow_neg, zpow_natCast]
          exact (one_le_inv₀ (pow_pos hg _)).mpr (pow_le_one₀ hg.le hup)
        change _ ≤ quoted Q D u μ orders σ τ extra w i.1
        rw [quoted, ← WilsonOriginalProjectedCurvatureEnvelope.commissioned Q D u μ orders N i.1 σ τ extra hL w]
        apply mul_le_mul_of_nonneg_right _ (gn i)
        simpa only [mul_one] using (mul_le_mul_of_nonneg_left power (Poly.worth hw ((Stock.census V).fire i.1.1.1)).le)
      · exact qn i.1
    · rw [tsum_fintype, invoice]
      change (∑i : Funded Q D u μ orders N σ, q i.1) ≤ ∑i : Rows, q i
      rw [← Finset.sum_subtype (p:=fun i : Rows => 0 < wallet Q D u μ orders N i σ)
        (univ.filter (fun i : Rows => 0 < wallet Q D u μ orders N i σ)) (fun i => by simp) q]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun i _ _ => qn i)

end YM.Integration.WilsonOriginalProjectedCurvatureCredits
