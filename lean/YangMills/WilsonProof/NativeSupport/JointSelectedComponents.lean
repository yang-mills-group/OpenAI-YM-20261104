import YangMills.WilsonProof.NativeSupport.JointComponentKernel
import YangMills.WilsonProof.NativeSupport.JointLeafTests

/-! Exact spatial separation on the original (shared-tag) measured ticket. -/
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
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

variable {ι : Type}
variable (M : ι→Lotus.Leaf R) (I : Tickets (Palette.sign M S))
variable (J : ι→Finset (Bond c)) (h : ι→Bond c→ℝ→ℝ)
variable (X : Coat T F)
variable (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
variable (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)

private def child (p : Molecule S) (W a : ℝ) (Ñ : ChartRatio G) (l : ℕ) :=
  bloom (team M (I.select p)) X (bonds J (I.select p).val) (probe J h (I.select p).val) W a Ñ l p

def froth (W a : ℝ) (Ñ : ChartRatio G) (l : ℕ) (V : Finset (Molecule S)) :=
  if joints T R l X.B V ∧ Matter.covers X V ∧ (team M I).signs S⊆V.biUnion id then
    ∏ p∈V,child M I J h X p W a Ñ l else 0

include H hk meas unit root in
private theorem spices (k : Finset ℕ) (V : Finset (Molecule S))
    (separate : joints T R Q.halo X.B V) (present : (team M I).signs S⊆V.biUnion id)
    (live : X.manifest) :
    steep (team M I) X (bonds J I.val) (probe J h I.val) k W o.a Q.table Q.halo (V.biUnion id) =
      ∏ p∈V,steep (team M (I.select p)) X (bonds J (I.select p).val)
        (probe J h (I.select p).val) k W o.a Q.table Q.halo p := by
  let K:=team M I
  let roster (p : Molecule S) := bonds J (I.select p).val
  let test (p : Molecule S) := probe J h (I.select p).val
  have covered : I.reach⊆V.biUnion id := (Palette.label M I) ▸ present
  have split (z : S.Choices) (v : F.Slice G × Air f G) :=
    JointLeaves.by_components J h I V (unweave separate) covered
      (fun b => lifted (X.taggedL z) R.beta b v)
  trans likely fun z : S.Choices => let A:=X.taggedL z
    ∫ v,(∏ p∈V,∏ b∈roster p,test p b (lifted A R.beta b v))*
      K.into A W o.a Q.table k Q.halo (V.biUnion id) v ∂((F.order G).prod A.dice)
  · apply congrArg likely
    funext z
    apply integral_congr_ae
    filter_upwards with v
    exact congrArg (·*K.into (X.taggedL z) W o.a Q.table k Q.halo (V.biUnion id) v) (split z v)
  have paid:=shared_tags K X H hk live k V separate present roster test
    (fun p _ _=> JointLeaves.measurable_probe J h (I.select p).val meas _)
    (fun p _ _=> JointLeaves.unit_probe J h (I.select p).val unit _)
    (fun p _=> JointLeaves.scope J X H M root (I.select p) p (I.selected p))
  refine paid.trans (prod_congr rfl fun p _ => ?_)
  change steep (K.locate p) X (roster p) (test p) k W o.a Q.table Q.halo p=_
  rw [show K.locate p=team M (I.select p) from Palette.localized M I p]

include H hk meas unit root in
theorem harvest (V : Finset (Molecule S)) (separate : joints T R Q.halo X.B V) :
    froth M I J h X W o.a Q.table Q.halo V =
      bourbon (team M I) X (bonds J I.val) (probe J h I.val) W o.a Q.table Q.halo (V.biUnion id) := by
  have ht:=cap_iff X separate
  unfold froth bourbon
  dsimp only at *
  simp_rw [ht]
  by_cases hp : Matter.covers X V ∧ ∀ i∈V,standsIn X R Q.halo i
  · rw [if_pos hp]
    let p := V.biUnion id
    let Y:= preps X (roster p)
    change _=steep (team M I) Y (bonds J I.val) (probe J h I.val) (Matter.own p) W o.a Q.table Q.halo p
    by_cases ha : (team M I).signs S ⊆ p
    · rw [spices M I J h Y H hk meas unit root (Matter.own p) V separate ha ((ht.2 hp).1.1),
        if_pos ⟨separate,hp.1,ha⟩]
      apply prod_congr rfl
      intro i hi
      exact scents (team M (I.select i)) X (bonds J (I.select i).val) (probe J h (I.select i).val) H hk
        (fun b _=> JointLeaves.measurable_probe J h (I.select i).val meas b)
        (fun b _=> JointLeaves.unit_probe J h (I.select i).val unit b) V separate
        (JointLeaves.scope J X H M root (I.select i) i (I.selected i)) hp.1 hi (hp.2 i hi)
    rw [if_neg (fun h=>ha h.2.2)]
    unfold steep
    have zero (z : S.Choices) := JointTicket.tithe_off (team M I) (Y.taggedL z)
      (bonds J I.val) (probe J h I.val) (Matter.own p) W o.a Q.table Q.halo p ha
    simp only [zero,likely_constant]
  rw [if_neg hp]
  split
  next hx =>
    obtain ⟨v,hv,ha⟩ : ∃ v∈V,¬standsIn X R Q.halo v := by by_contra! hh; exact hp ⟨hx.2.1,hh⟩
    exact prod_eq_zero hv (if_neg ha)
  rfl

include H hk meas unit root in
theorem street : HasSum (fun V : Finset (Molecule S)=> overhead X R Q.table *
    froth M I J h X W o.a Q.table Q.halo V)
    (JointPhysical.push S (bonds J I.val) (probe J h I.val) R.beta (team M I).cicada X.V) := by
  let f V:=overhead X R Q.table * froth M I J h X W o.a Q.table Q.halo V
  let g:=Ac.Parts H.supportP
  have he : Injective g:=LeftInverse.injective (show LeftInverse (fun t=>t.biUnion id) g from fun i=>Ac.reconstruct ..)
  apply (he.hasSum_iff (f:=f) ?_).1
  · refine (JointTicket.success (team M I) X (bonds J I.val) (probe J h I.val) H hk
      (fun b _=>JointLeaves.measurable_probe J h I.val meas b) (fun b _=>JointLeaves.unit_probe J h I.val unit b)).congr_fun fun p=>?_
    have hp : joints T R Q.halo X.B (g p):=⟨fun i hi=>(Ac.lives H.supportP p hi).2,Ac.separate ..⟩
    unfold f Function.comp
    dsimp only
    rw [harvest M I J h X H hk meas unit root _ hp,show (g p).biUnion id=p from Ac.reconstruct ..]
  intro i hi
  unfold f froth
  rw [if_neg (fun h=>hi ⟨_,separates h.1⟩),mul_zero]

end YM.Integration.InletSusceptibility.SelectedKernel
