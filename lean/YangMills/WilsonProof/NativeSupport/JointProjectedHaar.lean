import YangMills.WilsonProof.NativeSupport.JointPhysicalRecombine

/-! Read a permanent-set coefficient after the very same mounted tagged
Haar integration. Finite projection sums are exchanged only after
integrability has been proved for every individual colored coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
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
local notation "CC" => YM.Stock.census (Painted.Ink V)
variable (A : I→YM.MergeProof.Menu.Hat (YM.Stock.census (Painted.Ink V)) R) (w : Painted.Ink V→ℝ)
variable (J : V→Finset (Bond c)) (h : V→Bond c→ℝ→ℝ)
local notation "JJ" => (J ∘ (Prod.fst : Painted.Ink V→V))
local notation "hh" => (h ∘ (Prod.fst : Painted.Ink V→V))
local notation "leaves" => (fun i=>(A i).M)
local notation "names" => (fun i=>sing (A i) w)
local notation "fees" => (fun i=>sumFee (A i) w)
local notation "JJ₁" => (fun i=>bonds JJ (A i).s.val)
local notation "hh₁" => (fun i=>probe JJ hh (A i).s.val)
variable (H : Cash W x μ L Q o C T R) (Z : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b)) (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
local notation "factor" => (fun (k:S.Choices) (U:Config G f) (i:V)=>(JointPhysical.sample S k (J i) (h i) U Z:ℂ))

include H meas unit in
private theorem mounted_integrable (k:S.Choices) (s:Finset (Painted.Ink V)) :
    Integrable (fun U=>(taggedKernel S R.beta k U Z:ℂ)*
      (diagonal ((factor k U) ∘ Prod.fst) (Expense A w S U)).part (tag s)) (prior G f) := by
  let lp:=leaves
  let opt:=funds_branch H.laws.intake.ready
  let total (i:Tickets (Palette.sign lp S)) (U:Config G f):ℝ :=
    taggedKernel S R.beta k U Z*(∏ z∈s,JointPhysical.sample S k (J z.1) (h z.1) U Z)*(team lp i).cicada U
  let mark (i:Tickets (Palette.sign lp S)):ℂ:=((∏ j∈i.val,fees j:ℝ):ℂ)*(∏ j∈i.val,names j).part (tag s)
  have samples:Envelope (fun U:Config G f=>∏ z∈s,JointPhysical.sample S k (J z.1) (h z.1) U Z) := by
    induction s using Finset.induction with
    | empty => simp only [prod_empty];exact Envelope.const 1
    | @insert z s out ih =>
      simp only [prod_insert out]
      exact (JointPhysical.sample_env S k (J z.1) (h z.1) opt measurable_id measurable_const (meas _) (unit _)).mul ih
  have terms (i:Tickets (Palette.sign lp S)):Integrable (fun U=>((total i U:ℂ)*mark i)) (prior G f) := by
    have live:Envelope (total i) := ((env_tagged R.beta k opt measurable_id measurable_const).mul samples).mul
      ((team lp i).sells H.laws.intake.cap).1
    exact (Complex.ofRealCLM.integrable_comp (live.integrable _)).mul_const _
  refine (integrable_finsetSum univ fun i _=> terms i).congr ?_
  filter_upwards with U
  change _=(taggedKernel S R.beta k U Z:ℂ)*(diagonal _ (Merge.Photo.given (S:=S) lp fees CC names U)).part (tag s)
  simp only [on_part,Function.comp_apply,Merge.Photo.given,Poly.part_sum,Poly.part_smul,mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [total,mark,Complex.ofReal_mul,Complex.ofReal_prod]
  ring

include H meas unit in
theorem projected_haar (s:Finset V) :
    (Painted.project (SelectedKernel.given (S:=S) leaves JJ₁ hh₁ fees CC names Z)).part (tag s)=
      ∑ k:S.Choices,∫ U,(taggedKernel S R.beta k U Z:ℂ)*
        (diagonal (factor k U) (Painted.project (Expense A w S U))).part (tag s) ∂prior G f := by
  let kept:=univ.filter (fun S':Finset (Painted.Ink V)=>Painted.faithful S' ∧ S'.image Prod.fst=s)
  rw [Painted.projected_part]
  simp_rw [mounted_push A w JJ hh H Z (fun z=>meas z.1) (fun z=>unit z.1)]
  rw [sum_comm]
  refine sum_congr rfl fun k _=>?_
  change (∑ t∈kept,∫ U,(taggedKernel S R.beta k U Z:ℂ)*
    (diagonal ((factor k U) ∘ Prod.fst) (Expense A w S U)).part (tag t) ∂prior G f)=_
  rw [←integral_finsetSum kept (fun i _=>mounted_integrable A w J h H Z meas unit k i)]
  apply integral_congr_ae
  filter_upwards with U
  rw [←project_diagonal,Painted.projected_part]
  change _=_*(∑ i∈kept,_)
  rw [mul_sum]

include H meas unit in
theorem projected_live (s:Finset V) (k:(S).Choices) :
    Integrable (fun U=>(taggedKernel S R.beta k U Z:ℂ)*
      (diagonal (factor k U) (Painted.project (Expense A w S U))).part (tag s)) (prior G f) := by
  simp_rw [←project_diagonal,Painted.projected_part,mul_sum]
  exact integrable_finsetSum _ fun t _=>mounted_integrable A w J h H Z meas unit k t

end YM.Integration.InletSusceptibility.JointShadow
