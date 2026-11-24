import YangMills.WilsonProof.NativeSupport.JointMarkedValue
import YangMills.WilsonProof.NativeSupport.JointGauge
import YM.MergeProof.Lakes

/-! Exact original defect masks and held-field assays for measured regular and forced activities. -/
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
variable (Y : Cash W x μ L Q o C T R) (χ : Chi) (U : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (h i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖h i b e‖≤1)
variable (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)

open Blaze Refrain Letter OmitClusters Blaze.March Multiple Ursell Trees Mixed Daisy Gas
omit [Fintype ι] in
private theorem none_ticket (V : Config G c) (p : Molecule S) :
    JointTicket.act M Y χ V p (Tickets.none (Palette.sign M S))
      (bonds J (Tickets.none (Palette.sign M S)).val) (probe J h (Tickets.none (Palette.sign M S)).val)=Y.spawn χ V p := by
  rw [show bonds J (Tickets.none (Palette.sign M S)).val=∅ by simp [JointLeaves.bonds,Tickets.none],JointTicket.no_new,Palette.quiet]

theorem muted (V : Config G c) : color M J h Y χ V (fun _=>0)=Y.spawn χ V := by
  funext p
  unfold color
  rw [sum_eq_single (Tickets.none _),none_ticket]
  · simp [Tickets.none]
  · intro j _ ne
    obtain ⟨k,hk⟩:=Finset.nonempty_iff_ne_empty.mpr (show j.val≠∅ from fun e=>ne (Subtype.ext e))
    rw [prod_eq_zero hk rfl,zero_mul]
  simp

include meas unit in
omit [Fintype ι] in
private theorem absent (p : Molecule S) (I : Tickets (Palette.sign M S)) (bad : ¬I.reach⊆p) (V : Config G c) :
    JointTicket.act M Y χ V p I (bonds J I.val) (probe J h I.val)=0 := by
  have paid:=JointTicket.price M Y χ V p I (bonds J I.val) (probe J h I.val)
    (fun b _=>JointLeaves.measurable_probe J h I.val meas b) (fun b _=>JointLeaves.unit_probe J h I.val unit b)
  rw [if_neg bad] at paid
  exact norm_eq_zero.mp (le_antisymm paid (norm_nonneg _))

include meas unit in
theorem springs (V : Config G c) (i : Molecule S) (z : ι→ℝ) (hp : color M J h Y χ V z i≠0) :
    Ac.Spark Y.supportP i ∧ (roster i).flags=RG.flags (Pressure.temp x) V∩Y.unionP i ∧ (Y.unionP i).Nonempty := by
  letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  obtain ⟨p,hp'⟩ : ∃ p : Tickets (Palette.sign M S),JointTicket.act M Y χ V i p (bonds J p.val) (probe J h p.val)≠0 := by
    by_contra! blank
    apply hp
    unfold color
    simp_rw [blank,mul_zero,sum_const_zero]
  have hv : p.reach⊆i := by by_contra bad; exact hp' (absent M J h Y χ meas unit i p bad V)
  have he:=JointSwitch.present (F:=Classical.ofNonempty) M Y χ (fun t=>bonds J t.val) (fun t=>probe J h t.val) V p hp'
  have hf : Ac.Spark Y.supportP i:=he.1
  refine ⟨hf,he.2.2.symm,?_⟩
  by_cases hh:p.val.Nonempty
  swap
  · have hr:p=Tickets.none _:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hh)
    rw [hr,none_ticket] at hp'
    exact (Y.resident χ V _ hp').2.2.1
  obtain ⟨a,ha⟩:=hh
  let m:=M a
  have hpL:=m.turn.badge_area R T Q.halo (radiusB x)
  have hu : enlargement S.ratio Q.halo (radiusB x) (RG.inspected m.crest)⊆Y.unionP i:=
    hpL ▸ (show areas R T Q.halo (radiusB x) _ ⊆Y.unionP i from subset_biUnion_of_mem _ (hv (p.reaches_of ha)))
  refine Finset.Nonempty.mono hu (Finset.Nonempty.mono (halo_subset _ _) (Finset.Nonempty.image ?_ _))
  suffices H:m.crest.Nonempty from H.mono subset_union_left
  unfold Leaf.crest
  cases m.turn
  · exact ⟨_,(R.activities.reg _).anchor⟩
  exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup

include meas unit root in
theorem color_spin (θ : ι→ℝ) (i : Molecule S) :
    Measurable (fun V=>color M J h Y χ V θ i) ∧ UsesFinal (Pressure.temp x) (Y.unionP i) (fun V=>color M J h Y χ V θ i) ∧
      GaugeInvariant (fun V=>color M J h Y χ V θ i) := by
  let entry (p : Tickets (Palette.sign M S)) (V : Config G c) := JointTicket.act M Y χ V i p (bonds J p.val) (probe J h p.val)
  have he (p : Tickets (Palette.sign M S)) :
      UsesFinal (Pressure.temp x) (Y.unionP i) (entry p) ∧ GaugeInvariant (entry p) ∧ Measurable (entry p) := by
    by_cases fit : p.reach⊆i
    · exact held_outputs (bonds J p.val) (probe J h p.val)
        (fun b _=>JointLeaves.measurable_probe J h p.val meas b) (fun b _=>JointLeaves.unit_probe J h p.val unit b)
        M Y χ i p (JointLeaves.scope J (prism T x χ o.K 1 (Classical.choice (Tree.select S.ratio S.patch.odd_side))) Y M root p i fit)
    have off : entry p=(fun _=>0) := funext (absent M J h Y χ meas unit i p fit)
    rw [off]
    exact ⟨fun _ _ _ _=>rfl,fun _ _=>rfl,measurable_const⟩
  exact ⟨Finset.measurable_fun_sum _ (fun p _=>measurable_const.mul (he p).2.2),
    fun V U eq flags=>sum_congr rfl fun p _=>congrArg (_*·) ((he p).1 V U eq flags),
    fun z U=>sum_congr rfl fun p _=>congrArg (_*·) ((he p).2.1 z U)⟩
include meas unit root in
theorem smiling (θp : ι→ℝ) (V : Config G c) (p:Y.Chainbook):
    let g:= fun V=> Y.smilesMill V (color M J h Y χ V θp) p
    Measurable g∧ UsesFinal (Pressure.temp x) (Y.library p) g∧ GaugeInvariant g ∧ (g V≠0→ (Y.inventory p.1.toLeft).Nonempty∧ Y.statesPool V p∧Ac.Spark Y.bookFoot p.1):=by
  intro g
  let testAt:=h
  let Z:= fun V i=> Y.cologneMill (color M J testAt Y χ V θp) i; have hg(i:Y.Chapter): Measurable (fun V=> Z V i) ∧ UsesFinal (Pressure.temp x) (Y.bookFoot i) (fun V=>Z V i)∧GaugeInvariant (fun V=>Z V i):=by
    rcases i with i|i
    · exact color_spin M J testAt Y χ meas unit root θp i.val
    let u V j:= Y.entriesMill (color M J testAt Y χ V θp) (i.2 j); let a:ℝ:=Ursell.coefficient Y.seam i.2
    have h(z): Y.smallAt (i.2 z)⊆ Y.bookFoot (.inr i):= subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ _)
    refine ⟨(Measurable.neg ( (measurable_const (a:=a) |>.mul (Finset.measurable_fun_prod _ fun p _=> show Measurable (fun V=>u V p) from (color_spin M J testAt Y χ meas unit root θp _).1)).div_const ((i.fst+1).factorial:ℝ))),fun V U hV hb => ?_,fun t U=> ?_⟩
    · exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> inheritance ((color_spin M J testAt Y χ meas unit root θp _).2.1) (h j) V U hV hb)
    exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> (show u (gauge t U) j=u U j from (color_spin M J testAt Y χ meas unit root θp _).2.2 t U))
  refine ⟨?_ ,?_,?_,?_⟩
  · by_cases hv:Y.Fresh p∧ Ac.Spark Y.bookFoot p.1
    · let q(V : Config G c):=RG.flags (Pressure.temp x) V
      unfold g Cash.smilesMill; refine Measurable.ite ?_ (Finset.measurable_fun_prod _ (fun i _=>(( (hg i.val).1).pow_const _).div_const _)) measurable_const
      rw [show {V:Config G c| _}= ⋃ t∈ univ.filter (fun t=> Y.inventory p.fst.toLeft=t∩Y.library p),{V : Config G c|q V=t} from Set.ext (fun V:Config G c=> by simp [hv.1,hv.2,Cash.statesPool,q])]
      exact MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=>RG.flags_measurable_eq ..
    have ht : g=fun _=>0 := funext fun i=> if_neg (fun hx=>hv ⟨hx.1,hx.2.1⟩)
    rw [ht]; exact measurable_const
  · intro V U hv hl; unfold g Cash.smilesMill; have hu : Y.statesPool V p↔ Y.statesPool U p:=by unfold Cash.statesPool; rw [inter_comm, hl,inter_comm]
    simp_rw [hu]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ => t^(p.2 i+1)/↑(p.2 i+1).factorial) (inheritance ((hg i.1).2.1) (subset_biUnion_of_mem Y.bookFoot i.2) _ _ hv hl)
    rfl
  · intro t V; have hF : Y.statesPool (Lattice.gauge t V) p↔Y.statesPool V p:= by unfold Cash.statesPool; rw [gauge_flags]
    unfold g Cash.smilesMill; simp_rw [hF]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ=> t^(p.2 i+1)/↑(p.2 i+1).factorial) ((hg i.val).2.2 t V)
    rfl
  intro hc; unfold g Cash.smilesMill at hc; split at hc
  next h=>
    obtain ⟨i,hi⟩:= Y.regains p h.2.1 h.1
    exact ⟨Finset.Nonempty.mono (subset_biUnion_of_mem (fun i=> (roster (i:Y.ThickP).val).flags) (mem_toLeft.mpr hi)) i.2.2,h.2.2,h.2.1⟩
  next => exact (hc rfl).elim

end YM.Integration.InletSusceptibility.SelectedKernel
