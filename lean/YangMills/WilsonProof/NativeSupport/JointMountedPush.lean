import YangMills.WilsonProof.NativeSupport.JointShadow
import YangMills.WilsonProof.NativeSupport.JointMarkedValue
import YM.MergeProof.Plaza

/-! Exact insertion of newly born tests into the original numerical hat
expense.  Repeated labels on one bond use the very same tag and group field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Filter Finset MeasureTheory Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Census Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Merge Merge.Palette Greenbelt
open Marker Extra.Trajectories Packet JointCoat JointLeaves MergeProof.Menu
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {R : Rep G f} {W μ x C : ℝ} {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
local notation "B" => YM.Stock.census V
variable (A : I→YM.MergeProof.Menu.Hat (YM.Stock.census V) R) (w : V→ℝ) (J : V→Finset (Bond c)) (h : V→Bond c→ℝ→ℝ)

private def marks (i : I) : Finset (Bond c) := JointLeaves.bonds J (A i).s.val
private def tests (i : I) : Bond c→ℝ→ℝ := JointLeaves.probe J h (A i).s.val
private def factors (k : S.Choices) (U : Config G f) (Z : Config G c) (i : V) : ℂ :=
  (JointPhysical.sample S k (J i) (h i) U Z : ℝ)
private def names (i:I) : Marker.Poly (YM.Stock.census V) := YM.MergeProof.Menu.sing (A i) w
private def fees (i:I) : ℝ := YM.MergeProof.Menu.sumFee (A i) w
private def leaf (i:I) : Lotus.Leaf R := (A i).M

omit [Fintype I] in
private theorem mounted_product (k:S.Choices) (X : Config G f) (Z : Config G c)
    (I₀ : Tickets (Palette.sign (leaf A) S)) :
    diagonal (factors J h k X Z) (∏ i∈I₀.val,names A w i) =
      ((JointPhysical.sample S k (bonds (marks A J) I₀.val) (probe (marks A J) (tests A J h) I₀.val) X Z : ℝ):ℂ) •
       ∏ i∈I₀.val,names A w i := by
  let e (b : Bond c) := linkEnergy S (Z b*(S.prediction X k b)⁻¹)
  have each (i : I) : diagonal (factors J h k X Z) (names A w i) =
      ((JointPhysical.sample S k (marks A J i) (tests A J h i) X Z : ℝ):ℂ) • names A w i := by
    change diagonal _ (Poly.send (tag (A i).s.val) _) = _ • _
    rw [on_monomial]
    congr 1
    change (∏ j∈(A i).s.val,((∏ b∈J j,h j b (e b):ℝ):ℂ))= _
    rw [← Complex.ofReal_prod]
    exact congrArg Complex.ofReal (JointLeaves.flatten J h (A i).s.val e).symm
  rw [map_prod]
  simp_rw [each]
  rw [Finset.prod_smul,←Complex.ofReal_prod]
  congr 1
  exact congrArg Complex.ofReal (JointLeaves.flatten (marks A J) (tests A J h) I₀.val e).symm

variable (H : Cash W x μ L Q o C T R) (Z : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)

include H meas unit in
theorem mounted_push (p : (YM.Stock.census V).Mode) :
    (SelectedKernel.given (S:=S) (fun i=>(A i).M)
      (fun i=>JointLeaves.bonds J (A i).s.val)
      (fun i=>JointLeaves.probe J h (A i).s.val)
      (fun i=>sumFee (A i) w) B (fun i=>sing (A i) w) Z).part p =
      ∑ k:S.Choices, ∫ X,(taggedKernel S R.beta k X Z:ℂ)*
        (diagonal (fun i=>(JointPhysical.sample S k (J i) (h i) X Z : ℂ))
          (Expense A w S X)).part p ∂prior G f := by
  change (SelectedKernel.given (S:=S) (leaf A) (marks A J) (tests A J h) (fees A w) B (names A w) Z).part p =
      ∑ k:S.Choices, ∫ X, (taggedKernel S R.beta k X Z:ℂ)*
        (diagonal (factors J h k X Z) (Expense A w S X)).part p ∂prior G f
  let C₀ (i : Tickets (Palette.sign (leaf A) S)) := ((∏ j∈i.val,fees A w j:ℝ):ℂ)*(∏ j∈i.val,names A w j).part p
  let body (k : S.Choices) (i : Tickets (Palette.sign (leaf A) S)) :=
    JointPhysical.integrand S k (bonds (marks A J) i.val) (probe (marks A J) (tests A J h) i.val) R.beta (team (leaf A) i).cicada Z
  have ok := funds_branch H.laws.intake.ready
  have live (k : S.Choices) (i : Tickets (Palette.sign (leaf A) S)) :
      Integrable (fun X=> (body k i X:ℂ)*C₀ i) (prior G f) := by
    have e : Envelope (body k i) := ((env_tagged R.beta k ok measurable_id measurable_const).mul
      ((team (leaf A) i).sells H.laws.intake.cap).1).mul
      (JointPhysical.sample_env S k _ _ ok measurable_id measurable_const
        (fun b _=>JointLeaves.measurable_probe (marks A J) (tests A J h) i.val
          (fun j b _=>JointLeaves.measurable_probe J h (A j).s.val meas b) b)
        (fun b _=>JointLeaves.unit_probe (marks A J) (tests A J h) i.val
          (fun j b _=>JointLeaves.unit_probe J h (A j).s.val unit b) b))
    exact ((Complex.ofRealCLM.integrable_comp (e.integrable _))).mul_const _
  calc
    _ = ∑ i : Tickets (Palette.sign (leaf A) S), (∑ k:S.Choices, ∫ X,body k i X ∂prior G f : ℝ) * C₀ i := by
      unfold SelectedKernel.given
      simp only [Poly.part_sum,Poly.part_smul,Complex.ofReal_mul,mul_assoc]
      rfl
    _ = ∑ k:S.Choices, ∫ X,∑ i : Tickets (Palette.sign (leaf A) S),(body k i X:ℂ)*C₀ i ∂prior G f := by
      simp_rw [Complex.ofReal_sum,Finset.sum_mul,←integral_complex_ofReal,←integral_mul_const]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun k _=>(integral_finsetSum _ fun i _=> live k i).symm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards with X
      change _ = _*(diagonal _ (Merge.Photo.given (S:=S) (leaf A) (fees A w) B (names A w) X)).part p
      unfold Merge.Photo.given
      rw [map_sum, Poly.part_sum, Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      change _=_*(MarkerSubstitution.applyTo _ (_ • _)).part p
      rw [MarkerSubstitution.on_smul]
      change _=_*(_ • diagonal _ (∏ j∈i.val,names A w j)).part p
      rw [mounted_product,Poly.part_smul,Poly.part_smul]
      simp only [body,JointPhysical.integrand,C₀,Complex.ofReal_mul]
      ring

end YM.Integration.InletSusceptibility.JointShadow
