import YangMills.WilsonProof.NativeSupport.JointSelectedComponents

/-! The measured molecular gas sums to the original unnormalized tagged
Haar integral, for every fixed eligible kernel and every held coarse field. -/
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

variable {ι : Type} (M : ι→Lotus.Leaf R) (I : Tickets (Palette.sign M S))
variable (J : ι→Finset (Bond c)) (h : ι→Bond c→ℝ→ℝ)
variable (H : Cash W x μ L Q o C T R) (χ : Chi) (U : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
variable (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)

def blossom (V : Finset (Molecule S)) :=
  if joints T R Q.halo (radiusB x) V ∧ permitsA x U V ∧ (team M I).signs S⊆V.biUnion id then
    ∏ p∈V,JointTicket.act M H χ U p (I.select p) (bonds J (I.select p).val) (probe J h (I.select p).val) else 0

private theorem average {A B K : Type} (s : Finset A) (Y : A→Finset B)
    (dis : (s:Set A).PairwiseDisjoint Y) [Fintype B] [Fintype K] [Nonempty K] [P : Fintype (B→K)]
    (f : A→(B→K)→ℝ) (locality : ∀ i∈s,∀ u v,(∀ j∈Y i,u j=v j) → f i u=f i v) :
    (likely fun z => ∏ i∈s,f i z)=∏ i∈s,likely (f i) := by
  convert! Pond.jurisdictions s Y dis f locality

include meas unit root in
theorem together (V : Finset (Molecule S)) :
    (likely fun r : Greenbelt.Reserve S => froth M I J h (prism T x χ o.K U (allot r)) W o.a Q.table Q.halo V)=
      blossom M I J h H χ U V := by
  letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  let X (r : Greenbelt.Reserve S) := prism T x χ o.K U (allot r)
  let g (p : Molecule S) (r : Greenbelt.Reserve S) :=
    bloom (team M (I.select p)) (X r) (bonds J (I.select p).val) (probe J h (I.select p).val) W o.a Q.table Q.halo p
  by_cases hp : joints T R Q.halo (radiusB x) V ∧ permitsA x U V ∧ (team M I).signs S⊆V.biUnion id
  · have rows (r : Greenbelt.Reserve S) : froth M I J h (X r) W o.a Q.table Q.halo V=∏ p∈V,g p r := if_pos hp
    unfold blossom
    rw [if_pos hp]
    change (likely fun r : Greenbelt.Reserve S => froth M I J h (X r) W o.a Q.table Q.halo V)=_
    simp_rw [rows]
    let Y p:=ground R T Q.halo (radiusB x) p
    have independent (p : Molecule S) (_ : p∈V) (u v : Greenbelt.Reserve S) (eq : ∀ i∈Y p,u i=v i) :
        g p u=g p v := by
      have wood (i : Site f) (inside : S.ratio.parent i∈Y p) : (allot u).up i=(allot v).up i := by
        change (u _).up i=(v _).up i
        rw [eq _ inside]
      exact forest_bloom (team M (I.select p)) (X u) (bonds J (I.select p).val) (probe J h (I.select p).val) H rfl
        (fun b _=>JointLeaves.measurable_probe J h (I.select p).val meas b)
        (fun b _=>JointLeaves.unit_probe J h (I.select p).val unit b) (X v) p rfl rfl rfl rfl wood
        (JointLeaves.scope J (X u) H M root (I.select p) p (I.selected p))
    exact average V Y hp.1.2 g independent
  have rows (r : Greenbelt.Reserve S) : froth M I J h (X r) W o.a Q.table Q.halo V=0 := if_neg hp
  unfold blossom
  rw [if_neg hp]
  change (likely fun r : Greenbelt.Reserve S => froth M I J h (X r) W o.a Q.table Q.halo V)=_
  simp_rw [rows]
  exact likely_constant _

include meas unit root in
theorem summons (F' : Forest S.ratio) : HasSum (fun p : Finset (Molecule S) =>
    overhead (prism T x χ o.K U F') R Q.table * blossom M I J h H χ U p)
    (JointPhysical.push S (bonds J I.val) (probe J h I.val) R.beta (team M I).cicada U) := by
  letI : Nonempty (Forest S.ratio):=⟨F'⟩
  let X:=prism T x χ o.K U F'
  let Y (r : Greenbelt.Reserve S):=prism T x χ o.K U (allot r)
  have he r : overhead (Y r) R Q.table=overhead X R Q.table := TreeColor.overhead_eq (Y r) X rfl H.laws.intake.ready rfl Q.table R
  let reading:=JointPhysical.push S (bonds J I.val) (probe J h I.val) R.beta (team M I).cicada U
  have exactSeries:=Greenbelt.hasAvg _ (fun _ : Greenbelt.Reserve S=>reading)
    (fun r=>street M I J h (Y r) H rfl meas unit root)
  simp only [he,Greenbelt.likely_constant,Greenbelt.likely_mul] at exactSeries
  unfold Y at exactSeries
  simp_rw [together M I J h H χ U meas unit root] at exactSeries
  exact exactSeries

end YM.Integration.InletSusceptibility.SelectedKernel
