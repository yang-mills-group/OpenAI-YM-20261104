import YM.Integration.WilsonThermometerUnitFilingBlend

/-! The actual compact shape may be registered at one retained microscopic
site of each input tuple, shared by all eight faces. Its independent
coefficient is still evaluated at the original tuple. Its new filed
coordinate always belongs to this same registered cylinder. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRegistered
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato OPE OPE.Cards
open Bid RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof MergeProof.Accent FVA1 Marker
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingCylinder Primitives.GCC.Anchor
open WilsonThermometerUnitFilingReflectedShape (Key)
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) (z:UVIndex)
variable (r:ℝ) (φ:Test 3) (Q:Sites R z→Poly (Stock.census (Fin 3))) (place:Sites R z→Sites R z)
local notation "J!" => Stock.census (Fin 3)
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ
  (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
def submitted:Cut R.family z.1 z.2:=∑y,w! y • source R A z (place y) (Q y)
local notation "Y!" => submitted R A z r φ Q place
local notation "c!" => WilsonThermometerUnitFilingReflectedShape.tariff R z r φ Q
def operand (a:Key R z):Cut R.family z.1 z.2 := placed R A z a.2.val (place a.1)
local notation "F!" => operand R A z place

theorem expansion : (Y!)=∑a,c! a • (F!) a:=by
  rw [Fintype.sum_prod_type]
  unfold submitted
  apply Finset.sum_congr rfl;intro y _
  rw [source,Finset.smul_sum];apply Finset.sum_congr rfl;intro s _
  simp only [operand,WilsonThermometerUnitFilingReflectedShape.tariff,smul_smul]

private theorem smooth (a:Key R z) : Continuous ((F!) a):=by
  unfold operand placed;apply continuous_finsetProd;intro i _;exact R.family.continuousO ..

include simple in
theorem original {u b j:ℕ} (ju:j≤u) (ub:u≤b) (bN:b≤z.1) (door:Opened R.family 0 u z.2)
    (cost:Key R z→ℝ) (cap:ℝ) (pos:0≤cap)
    (prices:∀ y,w! y≠0 →∑s,‖wallet (Q y) s‖*cost (y,s)≤cap)
    (returned:∀a,c! a≠0 → ∃(E dR w:ℝ) (B:R.family.label 0) (q:store R.family 0 z.2 b),
      Funds R.family R.makes z.2 z.1 b 0 j u E dR w ((F!) a) ju ub bN door B q ∧
      2*(stakes R.family j u/w)+E/gainChart R.family.path b u≤cost a) :
    Booked R.family z.1 z.2 0 (Y!) u (ub.trans bN) ∧
    PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) ((∫x:Points 3,‖φ x‖)*cap)
      ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) ∧
    ‖R.family.omega z.1 z.2 (Y!)-report R (Y!) u‖ ≤ (∫x:Points 3,‖φ x‖)*cap :=by
  let T:=center R.family.S z.2 (ju.trans (ub.trans bN)) 0
  letI : Nonempty (Key R z) := ⟨(fun _=>0,⟨∅,Finset.mem_univ _⟩)⟩
  obtain ⟨book,root⟩:=WilsonThermometerUnitFilingBlend.original R simple (c!) (F!) ju ub bN door
    (smooth R A z place) cost returned
  have gain:∑a,‖c! a‖*cost a ≤(∫x:Points 3,‖φ x‖)*cap:=by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑y,‖w! y‖*cap :=by
        apply Finset.sum_le_sum;intro y _
        simp only [WilsonThermometerUnitFilingReflectedShape.tariff,norm_mul,mul_assoc,←Finset.mul_sum]
        by_cases hy:w! y=0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left (prices y hy) (norm_nonneg _)
      _ ≤ _ :=by
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (WilsonSeparatedOriginalThermometerCells.variation _ _ (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)) pos
  have change_field:=expansion R A z r φ Q place
  rw [←change_field] at root book
  refine ⟨book,⟨root.live,root.ticket,root.mark.trans gain⟩,?_⟩
  have bill:=((OPE.Strobe.atone T (R.family.beta z.1 z.2) (seamless R.makes z.1 z.2) root.ticket).trans root.mark).trans gain
  change ‖R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2))‖ ≤ _ at bill
  have law : R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) =
      R.family.omega z.1 z.2 (Y!) -report R (Y!) u :=by
    have nice:Continuous (Y!):=by
      rw [change_field,show (∑a,c! a • (F!) a)=_ from funext (fun V=>Finset.sum_apply V _ _)]
      exact continuous_finsetSum _ fun a _=>(smooth R A z place a).const_smul _
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact nice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  rw [law] at bill
  exact bill

end YM.Integration.WilsonThermometerUnitFilingRegistered
