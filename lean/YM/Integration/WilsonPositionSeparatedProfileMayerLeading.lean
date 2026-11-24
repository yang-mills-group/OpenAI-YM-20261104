import YM.RGLocalTaylor.Laminate.Winding

/-! Only the sector of the submitted heads can contribute a zero-decoration
coefficient. The surviving scalar is its genuine normalized tagged-coat moment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerLeading
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

theorem support {z:Molecule S} {M:ℕ} (u:Mayer.Decors z M) (degree:Mayer.decorOrder u=0) : z=∅:=by
  by_contra nonempty
  obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr nonempty
  have bound:=Finset.single_le_sum (f:=fun i:↥z=>(u i).val+1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨i,hi⟩:↥z))
  change (u ⟨i,hi⟩).val+1≤Mayer.decorOrder u at bound
  omega

/-- This vanishing requires no small-field bound or a local choice of forest. -/
theorem outside (prior:Team R) (p:Molecule S) (unselected:p≠prior.signs S) (V:Config G c) :
    Laminate.column prior p H (χ:=χ) M (0:Orders M) V=0:=by
  unfold Laminate.column
  by_cases admitted:prior.signs S⊆p
  · rw [if_pos admitted,if_neg (by simp)]
    unfold Laminate.scopeM
    split
    next=>unfold Mayer.coefficient;apply Finset.sum_eq_zero;intro u hit
          have empty:=support u (Finset.mem_filter.mp hit).2
          exact (unselected (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp empty) admitted)).elim
    rfl
  · rw [if_neg admitted];rfl

private theorem entered {p z:Molecule S} (empty:z=∅) (u:Mayer.Decors z M) (P:Head S→Insert T) (X:Coat T F) (a:momentSpace X) :
    Mayer.planned H p u P X a=∏h∈p,(P h).joint X a:=by
  letI:IsEmpty ↥z:=⟨fun i=>Finset.notMem_empty _ (empty.le i.property)⟩
  have sub:p\z=p:=by rw [empty,Finset.sdiff_empty]
  unfold Mayer.planned
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one,sub]

variable {η r q a Y D' A b v B C' ρ e uJ vJ θ K:ℝ}
/-- The survivor retains the same original unmarked gauge, forest and source
partner at every sampled point. -/
theorem measured (prior:Team R) (loc:H.ThinP) (minimal:loc.val=prior.signs S)
    (N:Captain H j C' D' Y B A b r a q n χ) (law:Awning H N.conduit A b ρ e uJ vJ k l)
    (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M) (inside:authorized H loc.val)
    (cohort:Mayer.Start loc.val) (V:Config G c) (healthy:Healthy (Pressure.temp s) (H.smallAt loc) V) :
    Laminate.column prior loc.val H (χ:=χ) M (0:Orders M) V=
      likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
        let X:=((planted (prism T s χ o.K V (Greenbelt.allot i)) loc.val).taggedL tag)
        ∫z,∏h∈loc.val,(Laminate.partner prior H h).joint X z ∂moment X:=by
  let rest:=loc.val\prior.signs S
  have empty:rest=∅:=by simp only [rest,minimal,Finset.sdiff_self]
  letI:IsEmpty ↥rest:=⟨fun i=>Finset.notMem_empty _ (empty.le i.property)⟩
  let u:Mayer.Decors rest M:=fun i=>isEmptyElim i
  have deg:Mayer.decorOrder u=0:=by simp only [Mayer.decorOrder,Finset.univ_eq_empty,Finset.sum_empty]
  have admitted:prior.signs S⊆loc.val:=by rw [minimal]
  have term:=Laminate.prescriptive (χ:=χ) (H:=H) (Y':=prior) loc N law room M 0 (0:Orders M) allow inside (Nat.zero_le _) rfl cohort admitted V healthy
  rw [term,Finset.sum_eq_single_of_mem u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,deg⟩) (fun v _ ne=>(ne (funext fun i=>isEmptyElim i)).elim)]
  congr 1;funext i;congr 1;funext tag
  apply integral_congr_ae;filter_upwards with z;exact entered empty u _ _ z

end YM.Integration.WilsonPositionSeparatedProfileMayerLeading
