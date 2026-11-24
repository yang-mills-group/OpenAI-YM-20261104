import YM.Integration.WilsonThermometerUnitFilingReflected
import YM.Integration.WilsonThermometerUnitFilingShape

/-! A single original reflected root at the measured fixed-date scalar of
the complete smooth thermometer. The face tickets need only exist on
actually used independent inverse coefficients and cutoff placements. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingReflectedShape
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato OPE OPE.Cards
open Bid RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof MergeProof.Accent FVA1 Marker
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingCylinder Primitives.GCC.Anchor
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6)
variable (z:UVIndex) (r:ℝ) (φ:Test 3) (Q:Sites R z→Poly (Stock.census (Fin 3)))
local notation "J!" => Stock.census (Fin 3)
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ
  (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
abbrev Key (R:Run G) (z:UVIndex):=Sites R z × (Stock.census (Fin 3)).Mode
def tariff (a:Key R z):ℂ:=w! a.1*wallet (Q a.1) a.2
def face (a:Key R z):Cut R.family z.1 z.2:=placed R A z a.2.val a.1

private theorem smooth (a:Key R z):Continuous (face R A z a):=by
  unfold face placed
  apply continuous_finsetProd;intro i _;exact R.family.continuousO .. 

theorem expansion : cylinder R A z r φ Q=∑ a,tariff R z r φ Q a • face R A z a := by
  rw [Fintype.sum_prod_type]
  unfold WilsonThermometerUnitFilingCylinder.cylinder
  apply Finset.sum_congr rfl;intro y _
  rw [source,Finset.smul_sum]
  apply Finset.sum_congr rfl;intro s _
  simp only [tariff,face,smul_smul]

def flat {u:ℕ} (live:u≤z.1) (Y:Cut R.family z.1 z.2) :=
  ((R.family.path.rep z.1 z.2 u).eval (1:Config G (R.family.side u z.2)):ℂ)⁻¹ *
    credit R.family z.1 z.2 0 Y u live 1

local notation "Y!" => cylinder R A z r φ Q
local notation "c!" => tariff R z r φ Q
local notation "F!" => face R A z

include simple in
private theorem split {u:ℕ} (live:u≤z.1) (door:Opened R.family 0 u z.2)
    (book:Booked R.family z.1 z.2 0 (Y!) u live) :
    report R (Y!) u=∑a,c! a*flat R z live (F! a) :=by
  rw [WilsonThermometerUnitFilingCourse.filed R simple _ door live book,expansion,
    IntrinsicProductLinearity.credit_sum R.family z.1 z.2 0 u live _ _ (smooth R A z),
    Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _=>by simp only [flat,Pi.smul_apply,smul_eq_mul];ring

private theorem restore {ι M:Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module ℂ M]
    (w:ι→ℂ) (f:ι→M):
    ∑a∈Finset.univ.filter (fun a=>w a≠0),w a • f a =∑a,w a • f a :=by
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro a _ outside
  have h:w a=0:=by simpa using outside
  simp [h]

private theorem envelope (cost:Key R z→ℝ) (cap:ℝ) (pos:0≤cap)
    (prices:∀ y,w! y≠0 →∑s,‖wallet (Q y) s‖*cost (y,s)≤cap):
    ∑a∈Finset.univ.filter (fun a=>c! a≠0),‖c! a‖*cost a≤(∫x:Points 3,‖φ x‖)*cap :=by
  have full:∑a∈Finset.univ.filter (fun a=>c! a≠0),‖c! a‖*cost a=∑a,‖c! a‖*cost a:=by
    apply Finset.sum_subset (Finset.filter_subset ..);intro a _ outside
    have h:c! a=0:=by simpa using outside
    simp [h]
  rw [full,Fintype.sum_prod_type]
  calc
    _ ≤ ∑y,‖w! y‖*cap := by
      apply Finset.sum_le_sum;intro y _
      simp only [tariff,norm_mul,mul_assoc,←Finset.mul_sum]
      by_cases h:w! y=0
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (prices y h) (norm_nonneg _)
    _ ≤ _ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation φ _ (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)) pos

include simple in
theorem original {u b j:ℕ} (ju:j≤u) (ub:u≤b) (bN:b≤z.1)
    (door:Opened R.family 0 u z.2) (book:Booked R.family z.1 z.2 0 (Y!) u (ub.trans bN))
    (cost:Key R z→ℝ) (cap:ℝ) (pos:0≤cap)
    (prices:∀ y,w! y≠0 →∑s,‖wallet (Q y) s‖*cost (y,s)≤cap)
    (returned:∀a,c! a≠0 → ∃(E dR w:ℝ) (B:R.family.label 0) (q:store R.family 0 z.2 b),
      Funds R.family R.makes z.2 z.1 b 0 j u E dR w (F! a) ju ub bN door B q ∧
      2*(stakes R.family j u/w)+E/gainChart R.family.path b u≤cost a) :
    PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) ((∫x:Points 3,‖φ x‖)*cap)
      ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) ∧
    ‖tested R A z r φ Q-report R (Y!) u‖ ≤ (∫x:Points 3,‖φ x‖)*cap :=by
  let live:=ub.trans bN
  let T:=center R.family.S z.2 (ju.trans live) 0
  let I:Finset (Key R z):=univ.filter fun a=>c! a≠0
  let f:=fun a=>F! a-flat R z live (F! a) • (1:Cut R.family z.1 z.2)
  have priced (a) (ha:a∈I):PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) (cost a) (f a):=by
    have ca:c! a≠0:=(Finset.mem_filter.mp ha).2
    obtain ⟨E,dR,w,B,q,fund,fee⟩:=returned a ca
    have true_price:=WilsonThermometerUnitFilingReflected.original R simple ju ub bN door (F! a) B q fund
    have filing:=WilsonThermometerUnitFilingCourse.filed R simple (F! a) door live (fund.works u le_rfl ub)
    change report R (F! a) u=flat R z live (F! a) at filing
    rw [filing] at true_price
    exact ⟨true_price.live,true_price.ticket,true_price.mark.trans fee⟩
  have calcify:(Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)=∑a∈I,c! a • f a:=by
    rw [show ∑a∈I,c! a • f a = ∑a,c! a • f a from restore _ _,split R simple A z r φ Q live door book,expansion]
    simp only [f,smul_sub,smul_smul,Finset.sum_sub_distrib,Finset.sum_smul]
  have roots:=Next.UVStress.root_sum T (R.family.beta z.1 z.2) I f (c!) (fun a ha=>(priced a ha).ticket)
    (seamless R.makes z.1 z.2)
  have total:PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) ((∫x:Points 3,‖φ x‖)*cap)
      ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)):=by
    rw [calcify]
    refine ⟨ju.trans live,roots.1,roots.2.trans ?_⟩
    exact (Finset.sum_le_sum fun a ha=>mul_le_mul_of_nonneg_left (priced a ha).mark (norm_nonneg _)).trans
      (envelope R z r φ Q cost cap pos prices)
  refine ⟨total,?_⟩
  have bill:=(OPE.Strobe.atone T (R.family.beta z.1 z.2) (seamless R.makes z.1 z.2) total.ticket).trans total.mark
  rw [←WilsonThermometerUnitFilingCylinder.literal R A z r φ Q]
  have law : R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) =
      R.family.omega z.1 z.2 (Y!)-report R (Y!) u :=by
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact (continuous_cylinder R A z r φ Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  change ‖R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2))‖ ≤ _ at bill
  rw [law] at bill
  exact bill

end YM.Integration.WilsonThermometerUnitFilingReflectedShape
