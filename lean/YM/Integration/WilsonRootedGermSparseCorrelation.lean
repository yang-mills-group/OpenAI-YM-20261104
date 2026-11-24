import YM.Integration.WilsonRootedGermDenseIncome

/-! The deposited old Wilson insertion against its full covariate after the measured flag-density cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermSparseCorrelation
open Function Finset Filter MeasureTheory Lattice Wilson RG Source MergeProof PhysicalNext.Repeat.Legato
open OPE.Therm Trace.Terrace IterationFour Trace.Physical.GermGraph Next.Rank.Price
open WilsonInheritedRegisteredField WilsonMatrixOriginalGermOccupancy WilsonRootedGermDenseIncome WilsonRootedGermFlagMass
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G)

/-- The original complex covariate on all fields below the paid count. -/
def sparse (e i p : ℕ) (D : Config G (R.family.side i p) → ℂ) (U : Config G (R.family.side i p)) : ℂ :=
  D U - slice R i p (load R e i p) D U

/-- The remaining sparse term keeps the signed, normalized hard observable and the actual test together. -/
theorem purchased (hG : G.Simple) (theta : Poetry R.family.path.levels) (e target : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ N p (live : i<N), R.family.ref 4 ≤ i →
      ∀ (w : R.family.label 4) (o : Site (R.family.side i p)) (B : ℝ),
      Next.UVStress.quota R.family 4 i N p w≤R.family.S.a i^4*B →
      ∀ D : Config G (R.family.side i p) → ℂ, Envelope D → ∀ M : ℝ, (∀ U, ‖D U‖≤M) →
      let μ := scene R.family.path N p i
      let Z := forced R.makes live.le w o
      Integrable (fun U=>Z U*D U) μ ∧ Integrable (fun U=>Z U*sparse R e i p D U) μ ∧
        ‖(∫ U,Z U*D U ∂μ) - (∫ U,Z U*sparse R e i p D U ∂μ)‖ ≤
          M*Real.exp (-(target:ℝ)*Lyra R.family.path.levels i) * (safety R.family i*stock R.family i*B) := by
  filter_upwards [WilsonRootedGermDenseIncome.purchased R hG theta e target] with i income
  intro N p live age w o B budget D hd M cap
  let μ : Measure (Config G (R.family.side i p)) := scene R.family.path N p i
  let Z : Config G (R.family.side i p) → ℂ := forced R.makes live.le w o
  letI : IsProbabilityMeasure μ := OPE.Therm.probability R.makes.wilson live.le
  let q := load R e i p
  let hot := slice R i p q D
  let cold := sparse R e i p D
  have hz : Envelope Z := marked R age live.le w o
  have eh : Envelope hot := slice_env R q hd
  have ec : Envelope cold := hd.subC eh
  have charged := income N p live.le o D hd M cap
  change (∫ U,rent R i N p o U*‖hot U‖ ∂μ)≤_ at charged
  rw [WilsonMatrixOriginalGermHeldTest.factor R live.le o hot] at charged
  have lb : 0≤B := nonneg_of_mul_nonneg_right ((Work.G08.size_nonneg _ _).trans budget) (pow_pos (R.family.S.a_pos i) 4)
  have dep : 0 ≤ safety R.family i*stock R.family i*B :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (stage R.family i).columns_ge)) lb
  have complete := (hz.mulC hd).integrableC μ
  have sparse_int := (hz.mulC ec).integrableC μ
  have split : (∫ U,Z U*D U ∂μ)-(∫ U,Z U*cold U ∂μ)=∫ U,Z U*hot U ∂μ := by
    rw [←integral_sub complete sparse_int]
    apply integral_congr_ae
    filter_upwards [] with U
    change Z U*D U-Z U*(D U-hot U)=Z U*hot U
    ring
  change Integrable (fun U=>Z U*D U) μ ∧ Integrable (fun U=>Z U*cold U) μ ∧ _
  refine ⟨complete,sparse_int,?_⟩
  change ‖(∫ U,Z U*D U ∂μ)-(∫ U,Z U*cold U ∂μ)‖ ≤ _
  rw [split]
  exact (norm_integral_le_integral_norm _).trans
    ((WilsonMatrixOriginalGermHeldTest.purchased R age live w o budget hot eh).trans (mul_le_mul_of_nonneg_right charged dep))

end YM.Integration.WilsonRootedGermSparseCorrelation
