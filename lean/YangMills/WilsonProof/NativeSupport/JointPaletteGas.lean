import YangMills.WilsonProof.NativeSupport.JointForestAverage

/-! Summing all mounted tickets recovers the measured original marked kernel. -/
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

def color (p : Molecule S) := ∑ i : Tickets (Palette.sign M S),(∏ j∈i.val,v j)*
  JointTicket.act M H χ U p i (bonds J i.val) (probe J h i.val)

def physical (β : ℝ) := ∑ i : Tickets (Palette.sign M S),(∏ j∈i.val,v j)*
  JointPhysical.push S (bonds J i.val) (probe J h i.val) β (team M i).cicada U

include meas unit in
omit [Fintype ι] in
private theorem reaches (i : Tickets (Palette.sign M S)) (p : Molecule S)
    (nz : JointTicket.act M H χ U p i (bonds J i.val) (probe J h i.val)≠0) : i.reach⊆p := by
  by_contra bad
  have paid:=JointTicket.price M H χ U p i (bonds J i.val) (probe J h i.val)
    (fun b _=>JointLeaves.measurable_probe J h i.val meas b) (fun b _=>JointLeaves.unit_probe J h i.val unit b)
  rw [if_neg bad] at paid
  exact nz (norm_eq_zero.mp (le_antisymm paid (norm_nonneg _)))

include meas unit in
theorem remit (A : Finset (Molecule S)) : H.festo U (color M J h H χ U v) A=
    ∑ p : Tickets (Palette.sign M S),(∏ j∈p.val,v j)*blossom M p J h H χ U A := by
  let l:=A.biUnion id
  by_cases good : joints T R Q.halo (radiusB x) A ∧ permitsA x U A
  swap
  · rw [show H.festo _ _ _=0 from if_neg good]
    symm
    exact sum_eq_zero fun i _=>by rw [blossom,if_neg (fun hi=>good ⟨hi.1,hi.2.1⟩),mul_zero]
  let f p (i : Tickets (Palette.sign M S)) := JointTicket.act M H χ U p i (bonds J i.val) (probe J h i.val)
  let g (i : Tickets (Palette.sign M S)) := ∏ j∈i.val,v j
  have confined (p : Molecule S) : color M J h H χ U v p =
      ∑ i : Tickets.Applies (Palette.sign M S) p,g i.val*f p i.val :=
    Tickets.confined _ _ (fun i hi=>reaches M J h H χ U meas unit i p (right_ne_zero_of_mul hi))
  let m (i : Tickets (Palette.sign M S)):=g i*blossom M i J h H χ U A
  have ht : (∑ i,m i)=∑ i : Tickets.Applies (Palette.sign M S) l,m i.val := Tickets.confined _ _ (fun a hi=>by
    rw [← Palette.label]; have hx:=right_ne_zero_of_mul hi
    unfold blossom at hx
    split at hx
    next H=>exact H.2.2
    next=>exact (hx rfl).elim)
  unfold Cash.festo
  dsimp only
  rw [if_pos good]
  change _=∑ i,m i
  rw [ht]
  simp_rw [confined]
  refine (Tickets.on_record (w:=Palette.sign M S) A id (unweave good.1) f v).trans ?_
  apply sum_congr rfl
  intro p _
  unfold m g blossom
  rw [if_pos (show _∧_∧_ from ⟨good.1,good.2,(Palette.label M p.val).symm ▸ p.prop⟩)]
  rfl

include meas unit root in
theorem pushed (F : Forest S.ratio) : HasSum (fun p=>overhead (prism T x χ o.K U F) R Q.table *
    H.festo U (color M J h H χ U v) p) (physical (S:=S) M J h U v R.beta) := by
  let g (p : Tickets (Palette.sign M S)):=∏ i∈p.val,v i
  have exactSum:=hasSum_sum (s:=univ)
    (fun i (_ : i∈(univ : Finset (Tickets (Palette.sign M S)))) =>
      (summons M i J h H χ U meas unit root F).mul_left (g i))
  apply exactSum.congr_fun
  intro p
  rw [remit M J h H χ U meas unit v,Finset.mul_sum]
  exact sum_congr rfl fun j _=>mul_left_comm ..

end YM.Integration.InletSusceptibility.SelectedKernel
