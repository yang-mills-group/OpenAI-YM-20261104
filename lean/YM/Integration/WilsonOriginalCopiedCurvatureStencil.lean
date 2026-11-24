import YM.Integration.WilsonOriginalClubSourcePackets
import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! The original inverse-tuned stencil, with the same couplings and tests on every lifted page. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCopiedCurvatureStencil
open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn PhysicalNext PhysicalNext.Repeat Legato
open Comparison.Density.RenderM FVA1Physical.TwoReset
open LocalComparison ComparisonDensity.Address WilsonOriginalProjectedCurvatureCredits
open ActualOriginalQPackets ActualOriginalQReaders WilsonOriginalProjectedCurvatureRoster
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureLamps
open scoped Classical BigOperators

section Copy
variable {G : Gauge} {n f : Side} {V : Type} {X : V → Type} {k : ℕ}
  [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
  (h : n.val ∣ f.val) (b : Fin (Pages n f))

/-- Replicate the previously named token. Every color, true path, test coefficient and fee
comes from the original finite Wilson stencil. -/
def lift (T : Token G n X k) : Token G f X k where
  root := (page h T.root b).val
  path := T.path
  gem := T.gem
  fall := T.fall
  plot := T.plot.image (fun z => (page h z b).val)
  coin := T.coin
end Copy

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ)
  {f : Side} (h : (R.family.side L p).val ∣ f.val)
  (b : Fin (Pages (R.family.side L p) f)) (g : ℝ) (x : tastes D) (U : Config G f)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) x
local notation "T" s:max => ActualOriginalQPackets.token Q D u μ orders N s
local notation "amp" s:max => ActualRunKernelPackets.amplitude R (ActualRunQlocalNativeTuple.orbit D)
  (degree u) N p L (labels Q D u μ orders N) s test
local notation "rootAt" s:max => (page h (ActualRunQlocalNativeTuple.root D s.1.1) b).val
local notation "Y" => cohort Q D u μ orders N σ extra

omit [Fintype V] [DecidableEq V] in
theorem token (s : Rows) :
    (lift h b (T s)).read test U = (((placed u s).unmasked U (rootAt s):ℝ):ℂ) * amp s := by
  unfold placed
  rw [WilsonOriginalProjectedCurvatureAtom.unmasked]
  apply NativeCurvatureTensor.token_read

omit [Fintype V] [DecidableEq V] in
private theorem workAt (s : Rows) (paid : 0 < (placed u s).budget σ) :
    (((divided (placed u s) σ).unmasked U (rootAt s) : ℝ) : ℂ) *
      paint Q D u μ orders N s σ x = (lift h b (T s)).read test U := by
  rw [token]
  unfold Atom.unmasked
  rw [poly]
  simp only [paint, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [mul_mul_mul_comm, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr paid.ne'), one_mul]
  rfl

theorem submitted (i : Funded Q D u μ orders N σ) :
    (FVA1Physical.TwoReset.copy h (Y i) b).nominal g x U =
      (g:ℂ) ^ (-(ActualRunKernelPackets.fieldRank R (degree u) i.1 : ℤ)) *
        (lift h b (T i.1)).read test U := by
  let s := i.1
  let J := divided (placed u s) σ
  change paint Q D u μ orders N s σ x *
    (↑(g ^ (WilsonOriginalProjectedCurvatureLoan.filed u s).lag * J.unmasked U (rootAt s)) : ℂ) = _
  rw [(WilsonOriginalProjectedCurvatureLoan.receipt u s).1, Complex.ofReal_mul, Complex.ofReal_zpow]
  rw [← workAt Q D u μ orders N σ h b x U s (substantial Q D u μ orders N s σ i.2)]
  ring

end YM.Integration.WilsonOriginalCopiedCurvatureStencil
