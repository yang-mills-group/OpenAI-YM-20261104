import YangMills.WilsonProof.NativeSupport.JointPaletteGas

/-! At each shared tag the numerical ticket variables acquire their original blocking-energy factors. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.SelectedKernel
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Census Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat JointLeaves JointTicket
open Merge Merge.Palette Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ x C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

variable {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf R)
variable (J : ι→Finset (Bond c)) (h : ι→Bond c→ℝ→ℝ)
variable (H : Cash W x μ L Q o C T R) (χ : Chi) (U : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
variable (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)

variable (v : ι→ℝ)

include H meas unit in
theorem physical_integral (β : ℝ) :
    physical (S:=S) M J h U v β =
      ∑ k : S.Choices,∫ X,taggedKernel S β k X U *
        Palette.buy M (fun i=>v i*JointPhysical.sample S k (J i) (h i) X U) S X ∂prior G f := by
  let rate (i : Tickets (Palette.sign M S)):=∏ j∈i.val,v j
  let body (k : S.Choices) (i : Tickets (Palette.sign M S)) :=
    JointPhysical.integrand S k (bonds J i.val) (probe J h i.val) β (team M i).cicada U
  have ok:=funds_branch H.laws.intake.ready
  have live (k : S.Choices) (i : Tickets (Palette.sign M S)) :
      Integrable (fun X=>rate i*body k i X) (prior G f) := by
    have bounded : Envelope (body k i) :=
      ((env_tagged β k ok measurable_id measurable_const).mul ((team M i).sells H.laws.intake.cap).1).mul
        (JointPhysical.sample_env S k (bonds J i.val) (probe J h i.val) ok measurable_id measurable_const
          (fun b _=>JointLeaves.measurable_probe J h i.val meas b) (fun b _=>JointLeaves.unit_probe J h i.val unit b))
    exact (bounded.integrable _).const_mul _
  change (∑ i,rate i*∑ k,∫ X,body k i X ∂prior G f)=_
  simp_rw [Finset.mul_sum,← integral_const_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← integral_finsetSum _ (fun i _=>live k i)]
  apply integral_congr_ae
  filter_upwards with X
  unfold Palette.buy
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  let e (b : Bond c):=linkEnergy S (U b*(S.prediction X k b)⁻¹)
  have split:=JointLeaves.flatten J h i.val e
  change (∏ j∈i.val,v j)*((taggedKernel S β k X U*(team M i).cicada X)*
    (∏ b∈bonds J i.val,probe J h i.val b (e b))) =
    taggedKernel S β k X U*((∏ j∈i.val,v j*∏ b∈J j,h j b (e b))*(team M i).cicada X)
  rw [split,Finset.prod_mul_distrib]
  ring

end YM.Integration.InletSusceptibility.SelectedKernel
