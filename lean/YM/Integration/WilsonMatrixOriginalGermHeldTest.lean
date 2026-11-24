import YM.Integration.WilsonMatrixOriginalGermContamination

/-! Test one complete original forced insertion against a bounded
spectator on its own earlier field. Both sides use the same genuine
Wilson normalization and the same full exterior activity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermHeldTest
open MeasureTheory Filter Lattice Wilson RG Source MergeProof PhysicalNext.Repeat.Legato OPE.Therm SectorNext.Vacuum
open WilsonInheritedRegisteredField WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermOccupancy
open WilsonMatrixOriginalGermForeground Trace.Physical.GermGraph Next.Rank.Price
open scoped BigOperators Classical
open private billed from YM.Integration.WilsonMatrixOriginalGermForeground
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
variable {G:Gauge} (R:Run G) {m N p:ℕ}

def allMarks (m N p:ℕ) (w:R.family.label 4) (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):ℂ:=
  let A:=R.family.path.rep N p m
  let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
  alto R.family.path m 4 * ∑' b,q.marked A b (pull 1 o U)

def fare (m N p:ℕ) (o:Site (R.family.side m p)) (D:Config G (R.family.side m p)→ℂ):ℝ:=
  let A:=R.family.path.rep N p m
  let Ξ:=partition G (R.family.side N p) (R.family.path.β N p N)
  ∫U,Real.exp (A.exponent U)*WilsonMatrixOriginalGermForeground.weight R m N p o U*‖D U‖/Ξ ∂prior G (R.family.side m p)

theorem factor (live:m≤N) (o:Site (R.family.side m p)) (D:Config G (R.family.side m p)→ℂ):
    (∫U,rent R m N p o U*‖D U‖ ∂scene R.family.path N p m)=fare R m N p o D:=by
  rw [OPE.Therm.account (H:=R.family.path) (p:=p) R.makes.wilson live (X:=ℝ)]
  apply integral_congr_ae
  filter_upwards [] with U
  dsimp only [fare,rent,OPE.Therm.dose,smul_eq_mul]
  rw [WilsonMatrixOriginalGermOccupancy.factor R live o U]
  field_simp [(partition_pos _).ne',(solvent R live o U).ne']

theorem signed (age : R.family.ref 4 ≤ m) (live:m≤N) (w:R.family.label 4) (o:Site (R.family.side m p))
    (D:Config G (R.family.side m p)→ℂ):
    let A:=R.family.path.rep N p m
    let Ξ:=partition G (R.family.side N p) (R.family.path.β N p N)
    (∫U,forced R.makes live w o U*D U ∂scene R.family.path N p m)=
      ∫U,((Real.exp (A.exponent U)/Ξ:ℝ):ℂ)*(allMarks R m N p w o U*D U) ∂prior G (R.family.side m p):=by
  intro A Ξ
  rw [OPE.Therm.account (H:=R.family.path) (p:=p) R.makes.wilson live (X:=ℂ)]
  apply integral_congr_ae
  filter_upwards [] with U
  have eq:forced R.makes live w o U*(vacuum R m N p o U:ℂ)=allMarks R m N p w o U:=billed R age live w o U
  rw [←eq]
  simp only [OPE.Therm.dose,Complex.real_smul,Complex.ofReal_div,WilsonMatrixOriginalGermOccupancy.factor R live o U,Complex.ofReal_mul]
  change _=((Real.exp (A.exponent U):ℂ)/Ξ)*_
  ring

private theorem weighted {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsFiniteMeasure μ] {h:Ω→ℝ}
    {D:Ω→ℂ} (hh:Envelope h) (hd:Envelope D):Integrable (fun U=>h U*‖D U‖) μ:=by
  obtain ⟨a,ha⟩:=hd.cost
  have bound:∀U,‖‖D U‖‖≤a:=fun U=>(Real.norm_of_nonneg (norm_nonneg _)).le.trans (ha U)
  simpa only [mul_comm] using (hh.integrable μ).bdd_mul hd.meas.norm.aestronglyMeasurable (Eventually.of_forall bound)

private theorem tested {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsFiniteMeasure μ]
    {T D:Ω→ℂ} {h:Ω→ℝ} {q:ℝ} (hT:Envelope T) (hD:Envelope D) (hh:Envelope h)
    (paid:∀x,‖T x‖≤h x*q):
    (∫x,‖T x*D x‖ ∂μ)≤(∫x,h x*‖D x‖ ∂μ)*q:=by
  rw [←integral_mul_const]
  apply integral_mono ((hT.mulC hD).integrableC μ).norm ((weighted μ hh hD).mul_const q)
  intro x
  change ‖T x*D x‖≤(h x*‖D x‖)*q
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (paid x) (norm_nonneg _)).trans_eq (by ring)

theorem purchased (age : R.family.ref 4 ≤ m) (interior:m<N) (w:R.family.label 4) (o:Site (R.family.side m p))
    {B:ℝ} (paid:Next.UVStress.quota R.family 4 m N p w≤R.family.S.a m^4*B)
    (D:Config G (R.family.side m p)→ℂ) (hD:Envelope D):
    (∫U,‖forced R.makes interior.le w o U*D U‖ ∂scene R.family.path N p m) ≤
      fare R m N p o D*(safety R.family m*stock R.family m*B):=by
  let μ:Measure (Config G (R.family.side m p)):=scene R.family.path N p m
  letI:IsProbabilityMeasure μ:=OPE.Therm.probability R.makes.wilson interior.le
  have result:=tested μ (marked R age interior.le w o) hD (bounded R interior o) (on_run R age interior.le w B paid o)
  exact result.trans_eq (congrArg (fun u=>u*(safety R.family m*stock R.family m*B)) (factor R interior.le o D))

end YM.Integration.WilsonMatrixOriginalGermHeldTest
