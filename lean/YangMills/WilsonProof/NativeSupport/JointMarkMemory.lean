import YangMills.WilsonProof.NativeSupport.JointForcedCode
import YM.MergeProof.Limb

/-! The measured source remembers its physical site. Erasing every fresh test recovers the original numerical switch exactly. -/
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
variable (J : ι→Finset (Bond c)) (test : ι→Bond c→ℝ→ℝ)
variable (Y : Cash W x μ L Q o C T R) (χ : Chi) (U : Config G c)
variable (meas : ∀ i,∀ b∈J i,Measurable (test i b))
variable (unit : ∀ i,∀ b∈J i,∀ e∈Set.Icc 0 (linkCap S),‖test i b e‖≤1)
variable (root : ∀ i,∀ b∈J i,S.ratio.embed b.1∈(M i).crest)

open Blaze Refrain Letter OmitClusters Blaze.March Multiple Ursell Trees Mixed Daisy Gas

theorem clear (z : ι→ℝ) (hz : ∀ i,z i ≠ 0 → J i=∅) :
    color M J test Y χ U z=Palette.color M Y χ U z := by
  funext p
  unfold color Palette.color
  refine sum_congr rfl fun I _=>?_
  by_cases h : ∃ i∈I.val,z i=0
  · obtain ⟨j,hj,hz⟩:=h
    rw [prod_eq_zero hj hz,zero_mul,zero_mul]
  have hb : bonds J I.val=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hmem
    obtain ⟨j,hj,hb⟩:=mem_biUnion.mp hmem
    rw [hz j (fun e=>h ⟨j,hj,e⟩)] at hb
    exact notMem_empty _ hb
  rw [hb,JointTicket.no_new]

variable (rA : ι→ℝ)
def vote (i : Molecule S) (V : Config G c) (t : ℝ) (Z : Finset ι) :=
  color M J test Y χ V (ways rA t Z) i
def song (i : Y.fragrances) (V : Config G c) (t : ℝ) (Z : Finset ι) :=
  Y.trainedMill (color M J test Y χ V (ways rA t Z)) i
def fete (i : Y.Chainbook) (V : Config G c) (t : ℝ) (Z : Finset ι) :=
  Y.smilesMill V (color M J test Y χ V (ways rA t Z)) i

include meas unit in
omit [Fintype ι] in
theorem mark_hit (V : Config G c) (u : Site c) (p : Molecule S) (I : Tickets (Palette.sign M S))
    (hv : JointTicket.act M Y χ V p I (bonds J I.val) (probe J test I.val)≠0)
    (j : ι) (hj : j∈I.val) (he : u∈(M j).crest.image S.ratio.parent) : u∈Y.unionP p := by
  have reach : I.reach⊆p := by
    by_contra absent
    have paid:=JointTicket.price M Y χ V p I (bonds J I.val) (probe J test I.val)
      (fun b _=>JointLeaves.measurable_probe J test I.val meas b) (fun b _=>JointLeaves.unit_probe J test I.val unit b)
    rw [if_neg absent] at paid
    exact hv (norm_eq_zero.mp (le_antisymm paid (norm_nonneg _)))
  have cover : areas R T Q.halo (radiusB x) (Palette.sign M S j) ⊆ Y.unionP p :=
    subset_biUnion_of_mem _ (reach (I.reaches_of hj))
  apply cover
  unfold Palette.sign
  rw [(M j).turn.badge_area]
  exact halo_subset _ _ (Finset.image_subset_image (s₂:=RG.inspected (M j).crest) Finset.subset_union_left he)

include meas unit
lemma forgotten (V:Config G c)(j:ι)(U:Site c)(he:U∈ (M j).crest.image S.ratio.parent)(i:Molecule S)(hz:U∉Y.unionP i)
    (t:ℝ)(Z:Finset ι): vote M J test Y χ rA i V t Z=vote M J test Y χ rA i V t (Z.erase j):=by
  unfold vote color; apply sum_congr rfl; intro v _
  by_cases hv:j∈v.val
  · rw [show JointTicket.act M Y χ V i v (bonds J v.val) (probe J test v.val)=0 from Classical.byContradiction (fun h=> hz (mark_hit M J test Y χ meas unit V U i v h j hv he)),mul_zero,mul_zero]
  exact congr_arg (·*_) (prod_congr rfl fun i hi=> by unfold ways; simp_rw [show i∈Z.erase j↔ i∈Z from (mem_erase.trans (and_iff_right (fun h=>hv (h ▸ hi))))]) -- DecPred
lemma limps (V:Config G c)(j:ι)(U:Site c)(he:U∈(M j).crest.image S.ratio.parent)(i:Y.fragrances)(hz:U∉Y.bookFoot (.inr i)) (t:ℝ)(Z:Finset ι): song M J test Y χ rA i V t Z=song M J test Y χ rA i V t (Z.erase j):= by
  refine congr_arg (fun v:ℝ=> (coefficient Y.seam i.2*v/↑(i.1+1).factorial)) (prod_congr rfl (fun p _=> ?_)); exact forgotten M J test Y χ meas unit rA V j U he (i.2 p).val (fun h=> hz (Finset.subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ p) h)) t Z
lemma limbs (V:Config G c)(j:ι)(U:Site c)(he:U∈(M j).crest.image S.ratio.parent)(i:Y.Chainbook)(hz:U∉Y.library i)(t:ℝ)(Z:Finset ι): fete M J test Y χ rA i V t Z=fete M J test Y χ rA i V t (Z.erase j):=by
  unfold fete Cash.smilesMill; split
  next hx=>
    refine Finset.prod_congr rfl fun y _=> congr_arg (fun t:ℝ=> t^(i.2 y+1)/↑(i.2 y+1).factorial) ?_
    rcases y with ⟨i'|i',hv⟩
    · exact forgotten M J test Y χ meas unit rA V j U he i'.val (fun h=> hz (Finset.subset_biUnion_of_mem Y.bookFoot hv h)) t Z
    exact congr_arg (- ·) (limps M J test Y χ meas unit rA V j U he i' (fun h=>hz (Finset.subset_biUnion_of_mem Y.bookFoot hv h)) t Z)
  rfl
include root in
lemma permits (i:Y.fragrances)(p:Finset ι)(t:ℝ) : let f V := song M J test Y χ rA i V t p
    let X:= Y.bookFoot (.inr i); UsesFinal (Pressure.temp x) X f ∧ Measurable f ∧ GaugeInvariant f ∧ ∀ V, f V≠0 → Healthy (Pressure.temp x) X V:=by
    intro g Z
    let u V j:= Y.entriesMill (color M J test Y χ V (ways rA t p)) (i.2 j); let a:ℝ:=Ursell.coefficient Y.seam i.2
    have h(z): Y.smallAt (i.2 z)⊆ Y.bookFoot (.inr i):= subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ _)
    refine ⟨fun V U hV hb=>?_,( (measurable_const (a:=a) |>.mul (Finset.measurable_fun_prod _ fun j _=> show Measurable (fun V=>u V j) from (color_spin M J test Y χ meas unit root (ways rA t p) _).1)).div_const ((i.fst+1).factorial:ℝ)),fun k U=> ?_,fun V hx=>?_⟩
    · exact congr_arg (fun v:ℝ=> a*v/↑(i.1+1).factorial) (prod_congr rfl fun j _=> inheritance ((color_spin M J test Y χ meas unit root _ _).2.1) (h j) V U hV hb)
    · exact congr_arg (fun v:ℝ=> a*v/↑(i.1+1).factorial) (prod_congr rfl fun j _=> (show u (gauge k U) j=u U j from (color_spin M J test Y χ meas unit root _ _).2.2 k U))
    refine Finset.disjoint_left.mpr ?_; intro z hz hp; obtain ⟨j,hj,hq⟩:= mem_biUnion.mp hz
    have ht : u V j ≠0 := fun h => hx (by unfold g song Cash.trainedMill Gas.term; rw [prod_eq_zero (mem_univ j) h,mul_zero,zero_div]); have he:= (springs M J test Y χ meas unit V (i.2 j).val _ ht).2.1; rw [(i.2 j).2.2] at he; exact Finset.notMem_empty _ (he.symm ▸ (show z∈RG.flags _ _∩ _ from mem_inter.mpr ⟨hp,hq⟩))

end YM.Integration.InletSusceptibility.SelectedKernel
