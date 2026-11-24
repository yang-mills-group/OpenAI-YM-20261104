import YM.Integration.WilsonMatrixOriginalGermForeground
import YM.Integration.SelectedCofactorLocalProjection

/-! The rough-flag rent in the charged original Wilson law. The exponent is unchanged by
translation of the anchor. One copy of the physical density cancels one gas divisor. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermOccupancy
open MeasureTheory Lattice Wilson RG MergeProof Push.Local
open PhysicalNext.Repeat.Legato
open SectorNext.Vacuum WilsonMatrixOriginalGermForeground
open scoped Classical
variable {G:Gauge} (R:Run G) {m N p:ℕ}

def rent (m N p:ℕ) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):ℝ:=
  WilsonMatrixOriginalGermForeground.weight R m N p o U / vacuum R m N p o U

theorem rent_nonneg (live:m≤N) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    0≤rent R m N p o U:=by
  apply div_nonneg _ (solvent R live o U).le
  dsimp only [WilsonMatrixOriginalGermForeground.weight];split <;> positivity

theorem factor (live:m≤N) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    let A:=R.family.path.rep N p m
    A.eval U=Real.exp (A.exponent U)*vacuum R m N p o U:=by
  let A:=R.family.path.rep N p m
  obtain ⟨shift⟩:Nonempty (A.activities.Moves 1 o):=(R.makes.wilson.represents N p m live).good.labels.moves 1 o
  have eval:A.eval (pull 1 o U)=A.eval U:=eval_pull shift U
  have expo:=Push.Local.exponent_pull shift U
  change A.eval U=Real.exp (A.exponent U)*vacuum R m N p o U
  rw [←eval]
  change Real.exp (A.exponent (pull 1 o U))*_=_
  rw [expo];rfl

private theorem weights {o:Site (R.family.side m p)}:Envelope (WilsonMatrixOriginalGermForeground.weight R m N p o):=by
  let A:=R.family.path.rep N p m
  let fw:Support (R.family.side m p)→ℝ:=fun T=>if T=∅ then 0 else Real.exp (-flagRate A.p*T.card)
  have mf:Measurable fun U:Config G (R.family.side m p)=>flags A.p.threshold U:=by
    apply measurable_to_countable _;intro i;exact flags_measurable_eq ..
  have mf':Measurable fw:=measurable_of_countable fw
  refine ⟨mf'.comp (mf.comp (continuous_pull 1 o).measurable),1,fun U=>?_⟩
  dsimp only [WilsonMatrixOriginalGermForeground.weight];split
  · simp
  · rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (flagRate_pos _).le) (Nat.cast_nonneg _))

/-- The fixed finite floor only establishes integrability. It does not enter the price. -/
theorem bounded (interior:m<N) (o:Site (R.family.side m p)):Envelope (rent R m N p o):=by
  let A:=R.family.path.rep N p m
  have law:=(R.makes.wilson.represents N p m interior.le).good
  have num:Envelope (fun U=>WilsonMatrixOriginalGermForeground.weight R m N p o U*Real.exp (A.exponent U)):=(weights R).mul (A.exponentEnv law).exp
  have den:Envelope A.eval:=A.envelope law
  obtain ⟨a,ha,floor⟩:=SelectedCofactorLocalProjection.floor (C:=R.family) (p:=p) R.makes interior
  have eq:rent R m N p o=fun U=>WilsonMatrixOriginalGermForeground.weight R m N p o U*Real.exp (A.exponent U)/A.eval U:=by
    funext U
    have ev: A.eval U=Real.exp (A.exponent U)*vacuum R m N p o U:=factor R interior.le o U
    unfold rent;rw [ev];field_simp [(Real.exp_pos (A.exponent U)).ne',(solvent R interior.le o U).ne']
  rw [eq]
  obtain ⟨K,cap⟩:=num.cost
  refine ⟨num.meas.div den.meas,K/a,fun U=>?_⟩
  rw [norm_div,Real.norm_eq_abs (A.eval U),abs_of_pos (ha.trans_le (floor U))]
  exact div_le_div₀ ((norm_nonneg _).trans (cap U)) (cap U) ha (floor U)

theorem prior (live:m≤N) (o t:Site (R.family.side m p)):
    let A:=R.family.path.rep N p m
    let Ξ:=partition G (R.family.side N p) (R.family.path.β N p N)
    (∫U,rent R m N p o U ∂OPE.Therm.scene R.family.path N p m) =
        ∫U,Real.exp (A.exponent U)*WilsonMatrixOriginalGermForeground.weight R m N p o U/Ξ ∂prior G (R.family.side m p) ∧
    (∫U,rent R m N p o U*rent R m N p t U ∂OPE.Therm.scene R.family.path N p m) =
        ∫U,Real.exp (A.exponent U)*WilsonMatrixOriginalGermForeground.weight R m N p o U*WilsonMatrixOriginalGermForeground.weight R m N p t U/(Ξ*vacuum R m N p t U) ∂prior G (R.family.side m p):=by
  let A:=R.family.path.rep N p m
  let Ξ:=partition G (R.family.side N p) (R.family.path.β N p N)
  have acct:=OPE.Therm.account (H:=R.family.path) (p:=p) R.makes.wilson live (X:=ℝ)
  dsimp only
  constructor <;> rw [acct] <;> apply integral_congr_ae <;> filter_upwards [] with U <;>
    simp only [smul_eq_mul,OPE.Therm.dose,rent] <;> rw [factor R live o U] <;>
    field_simp [(partition_pos _).ne',(solvent R live o U).ne',(solvent R live t U).ne']

end YM.Integration.WilsonMatrixOriginalGermOccupancy
