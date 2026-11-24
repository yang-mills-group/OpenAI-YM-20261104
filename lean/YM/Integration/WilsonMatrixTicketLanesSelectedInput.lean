import YM.Integration.WilsonReportingPrescribedOldMicroscopic
import YM.Integration.WilsonReportingPrescribedOldScale
import YM.Integration.WilsonReportingMeasuredWardFunding
import YM.Integration.WilsonSeparatedOriginalSlabQArms

/-! All proper faces, including the vacuum, of the original prescribed marked input
at its reporting clock. The cut of the prior may be arbitrarily later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesSelectedInput
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Marker Precision
open IterationFour.Vacuum LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open Push.GridApprox MergeProof MergeProof.Accent RG3.Script.Picnic FullQLocal.RenderedStep
open ActualOriginalQReaders
open private reader from YM.Integration.WilsonReportingPrescribedOldScale
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical BigOperators
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R:Run G) (J:Request V) (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J
local notation "β" => R.family.path.levels.clock.hatBeta

def source (simple:G.Simple) {m N per:ℕ} (life:m+1≤N) (o:V→Site (R.family.side (m+1) per))
    (clock:ℝ) (r:V→ℕ) (x:IndependentTests (ActualRunQlocalNativeTuple.orbit (D per (m+1) o)))
    (U:Config G (R.family.side (m+1) per)):Poly (Stock.census V):=
  ((R.family.path.rep N per (m+1)).eval U)⁻¹ •
    ((ActualOriginalQInput.input Q (D per (m+1) o) u clock r simple N life).leaf (testInclusion _ x)).density U

theorem component (simple:G.Simple) {m N per:ℕ} (life:m+1≤N) (o:V→Site (R.family.side (m+1) per))
    (age:∀a:Slot u,R.family.ref a.2.size ≤ m + 1) (clock:ℝ) (r:V→ℕ)
    (x:IndependentTests (ActualRunQlocalNativeTuple.orbit (D per (m+1) o))) (s:(Stock.census V).Mode)
    (U:Config G (R.family.side (m+1) per)):
    (source R J Q u simple life o clock r x U).part s=
      ∏i∈s.val,ActualRunQlocalNativeTuple.reader (D per (m+1) o) i (testInclusion _ x i)*
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) clock _ (ActualRunQlocalNativeTuple.root (D per (m+1) o) i) U (r i):=by
  have h:=WilsonReportingPrescribedOldMicroscopic.stated R Q (D per (m+1) o) u clock r simple life age (testInclusion _ x) s U
  have hp:0<(R.family.path.rep N per (m+1)).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson life U
  have realPart(t:ℝ)(b:Poly (Stock.census V)):(t • b).part s=t • b.part s:=rfl
  rw [source,realPart,h,inv_smul_smul₀ hp.ne']
  rfl

/-- One price before all cutoffs and all periods, for each actual state,
and then the full weighted polynomial, including both proper marginal sectors. -/
theorem purchased (simple:G.Simple) (K:ℕ) (μ:ℝ):
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀{m N per:ℕ}(life:m+1≤N)(o:V→Site (R.family.side (m+1) per))
      (_age:∀a:Slot u,R.family.ref a.2.size ≤ m + 1)(r:V→ℕ), (∀i,r i≤K) →
      ∀(x:IndependentTests (ActualRunQlocalNativeTuple.orbit (D per (m+1) o)))(U:Config G (R.family.side (m+1) per)),
      let f:=source R J Q u simple life o (μ-R.family.S.scale (m+1)) r x U
      (∀s:(Stock.census V).Mode,‖f.part s‖≤(C*β (m+1)^e)^s.val.card) ∧
      ∀w:V→ℝ,(∀i,0≤w i)→Poly.price w f≤∑s:(Stock.census V).Mode,Poly.toll w s*(C*β (m+1)^e)^s.val.card:=by
  obtain ⟨a,ap,n,atoms⟩:=WilsonSeparatedOriginalSlabQArms.fixed R Q u K μ
  obtain ⟨g,gp,scale⟩:=date R simple
  let bound:=1+∑i:V,‖readerPrice (D 0 0 (fun _=>0)) i‖
  have bp:0<bound:=by dsimp [bound]; positivity
  refine ⟨bound*(a*g^n),by positivity,n,?_⟩
  intro m N per life o age r rank x U
  dsimp only
  have hp:0<β (m+1):=zero_lt_one.trans (R.family.path.levels.fits.delayed (m+1))
  have gross(i:V):readerPrice (D per (m+1) o) i≤bound:=by
    rw [reader R J per (m+1) o i]
    have hi:‖readerPrice (D 0 0 (fun _=>0)) i‖≤∑j:V,‖readerPrice (D 0 0 (fun _=>0)) j‖:=
      Finset.single_le_sum (fun j _=>norm_nonneg _) (Finset.mem_univ i)
    dsimp only [bound]
    linarith only [Real.le_norm_self (readerPrice (D 0 0 (fun _=>0)) i),hi]
  have slot(i:V):‖ActualRunQlocalNativeTuple.reader (D per (m+1) o) i (testInclusion _ x i)*
      ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-R.family.S.scale (m+1)) _ (ActualRunQlocalNativeTuple.root (D per (m+1) o) i) U (r i)‖≤
      bound*(a*g^n)*β (m+1)^n:=by
    have dr:=(native_reader_bound (D per (m+1) o) i x).trans (gross i)
    have pr:=(atoms i (r i) (rank i) (R.family.S.scale (m+1)) (R.family.side (m+1) per) (ActualRunQlocalNativeTuple.root (D per (m+1) o) i) U).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (scale (m+1)) n) ap.le)
    rw [norm_mul]
    have h:=mul_le_mul dr pr (norm_nonneg _) bp.le
    simpa only [mul_pow,mul_assoc] using h
  have faces(s:(Stock.census V).Mode):
      ‖(source R J Q u simple life o (μ-R.family.S.scale (m+1)) r x U).part s‖≤(bound*(a*g^n)*β (m+1)^n)^s.val.card:=by
    rw [component R J Q u simple life o age, norm_prod]
    calc _ ≤ ∏ _∈s.val,(bound*(a*g^n)*β (m+1)^n) := Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>slot i)
         _ = _ := Finset.prod_const _
  refine ⟨faces,fun w hw=>?_⟩
  exact Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_left (faces s) (Finset.prod_nonneg fun i _=>hw i)

end YM.Integration.WilsonMatrixTicketLanesSelectedInput
