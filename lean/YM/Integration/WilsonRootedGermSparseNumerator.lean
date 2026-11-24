import YM.Integration.WilsonRootedGermDose

/-! The signed sparse term is the actual unnormalized previous one-hole marginal on Haar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermSparseNumerator
open Function Finset Filter MeasureTheory Lattice Wilson RG Source MergeProof PhysicalNext.Repeat.Legato
open OPE.Therm Trace.Terrace IterationFour Trace.Physical.GermGraph Next.Rank.Price
open WilsonMatrixOriginalGermForeground WilsonInheritedRegisteredField WilsonMatrixOriginalGermOccupancy WilsonMatrixOriginalGermHeldTest
open WilsonRootedGermSparseCorrelation WilsonRootedGermDenseIncome WilsonRootedGermFlagMass
open private billed from YM.Integration.WilsonMatrixOriginalGermForeground
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {i N p : ℕ}

def numerator (i N p : ℕ) (w : R.family.label 4) (o : Site (R.family.side i p))
    (D : Config G (R.family.side i p)→ℂ) (U : Config G (R.family.side i p)) : ℂ :=
  let W := R.family.path.rep N p i
  let Ξ := partition G (R.family.side N p) (R.family.path.β N p N)
  ((Real.exp (W.exponent U)/Ξ:ℝ):ℂ)*(allMarks R i N p w o U*D U)

/-- The exact original normalized Haar operand is integrable even at the terminal date. -/
theorem integrable (age : R.family.ref 4 ≤ i) (live : i≤N) (w : R.family.label 4) (o : Site (R.family.side i p))
    (D : Config G (R.family.side i p)→ℂ) (hd : Envelope D) : Integrable (numerator R i N p w o D) (prior G (R.family.side i p)) := by
  let W := R.family.path.rep N p i
  let Ξ := partition G (R.family.side N p) (R.family.path.β N p N)
  have pos : 0<Ξ := partition_pos _
  have he := W.envelope (R.makes.wilson.represents N p i live).good
  have dose : Envelope (fun U=>((W.eval U/Ξ:ℝ):ℂ)) := by
    obtain ⟨M,hM⟩ := he.cost
    refine ⟨Complex.measurable_ofReal.comp (he.meas.div_const Ξ),M/Ξ,fun U=>?_⟩
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos pos] using div_le_div_of_nonneg_right (hM U) pos.le
  apply (dose.mulC ((marked R age live w o).mulC hd)).integrableC (prior G (R.family.side i p)) |>.congr
  filter_upwards [] with U
  have previous : forced R.makes live w o U*(vacuum R i N p o U:ℂ)=allMarks R i N p w o U := billed R age live w o U
  have at_field : W.eval U=Real.exp (W.exponent U)*vacuum R i N p o U := WilsonMatrixOriginalGermOccupancy.factor R live o U
  change ((W.eval U/Ξ:ℝ):ℂ)*(forced R.makes live w o U*D U)=((Real.exp (W.exponent U)/Ξ:ℝ):ℂ)*(allMarks R i N p w o U*D U)
  simp only [←previous,at_field,Complex.ofReal_div,Complex.ofReal_mul]
  ring

/-- Cut the positive heat payment only on the dense complement. The remaining signed sum is evaluated in Haar. -/
theorem purchased (hG : G.Simple) (theta : Poetry R.family.path.levels) (e target : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ N p (live : i≤N), R.family.ref 4 ≤ i →
      ∀ (w : R.family.label 4) (o : Site (R.family.side i p)) (B : ℝ),
      Next.UVStress.quota R.family 4 i N p w≤R.family.S.a i^4*B →
      ∀ D : Config G (R.family.side i p) → ℂ, Envelope D → ∀ M : ℝ, (∀ U, ‖D U‖≤M) →
      let μ := scene R.family.path N p i
      let Z := forced R.makes live w o
      let Y := numerator R i N p w o (sparse R e i p D)
      Integrable (fun U=>Z U*D U) μ ∧ Integrable Y (prior G (R.family.side i p)) ∧
        ‖(∫ U,Z U*D U ∂μ) - (∫ U,Y U ∂prior G (R.family.side i p))‖ ≤
          M*Real.exp (-(target:ℝ)*Lyra R.family.path.levels i)*(safety R.family i*stock R.family i*B) := by
  filter_upwards [WilsonRootedGermDenseIncome.purchased R hG theta e target] with i income
  intro N p live age w o B budget D hd M cap
  let μ : Measure (Config G (R.family.side i p)) := scene R.family.path N p i
  let Z : Config G (R.family.side i p)→ℂ := forced R.makes live w o
  letI : IsProbabilityMeasure μ := OPE.Therm.probability R.makes.wilson live
  let hot := slice R i p (load R e i p) D
  let cold := sparse R e i p D
  have hz : Envelope Z := marked R age live w o
  have eh : Envelope hot := slice_env R _ hd
  have ec : Envelope cold := hd.subC eh
  have charged := income N p live o D hd M cap
  change (∫ U,rent R i N p o U*‖hot U‖ ∂μ)≤_ at charged
  rw [factor R live o hot] at charged
  have lb : 0≤B := nonneg_of_mul_nonneg_right ((Work.G08.size_nonneg _ _).trans budget) (pow_pos (R.family.S.a_pos i) 4)
  have dep : 0 ≤ safety R.family i*stock R.family i*B := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (stage R.family i).columns_ge)) lb
  have full := (hz.mulC hd).integrableC μ
  have sparse_int := (hz.mulC ec).integrableC μ
  have split : (∫ U,Z U*D U ∂μ)-(∫ U,Z U*cold U ∂μ)=∫ U,Z U*hot U ∂μ := by
    rw [←integral_sub full sparse_int]
    apply integral_congr_ae
    filter_upwards [] with U
    change Z U*D U-Z U*(D U-hot U)=Z U*hot U
    ring
  refine ⟨full, integrable R age live w o cold ec,?_⟩
  change ‖(∫ U,Z U*D U ∂μ)-(∫ U,numerator R i N p w o cold U ∂prior G (R.family.side i p))‖≤_
  have field : (∫ U,Z U*cold U ∂μ)=(∫ U,numerator R i N p w o cold U ∂prior G (R.family.side i p)) := signed R age live w o cold
  rw [←field,split]
  exact (norm_integral_le_integral_norm _).trans ((WilsonRootedGermDose.held R age live w o budget hot eh).trans (mul_le_mul_of_nonneg_right charged dep))

end YM.Integration.WilsonRootedGermSparseNumerator
