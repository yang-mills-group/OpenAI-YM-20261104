import YM.OPE.Compatible.Yolk.Jewel
/-!
# For any ray. Drape-only gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
lemma Leaf.harmless (M:Leaf S R) {i:ℕ}(h:M.turn=Wing.logKey i)(U:Config G f):M.cicada U=R.eval U*M.ingredient U:=by
  have he p:M.bun p U=R.activities.gasOccurrence R.p p U*M.ingredient U:=by unfold Leaf.bun Leaf.bill Activities.gasOccurrence; split; rw [h,if_pos (show Wing.Occupied (.logKey _) _ from trivial)]; exact mul_comm ..; simp
  unfold Leaf.cicada; simp_rw [he,tsum_mul_right]; unfold Rep.eval Activities.gas; rw [← mul_assoc]
lemma smolder (U:Config G f){Z:Support f}(h:¬Healthy R.p.threshold Z U):R.eval U=smudge R Z U:=by
    unfold smudge Rep.eval Activities.gas; rw [← tsum_mul_left]; apply tsum_congr; intro i
    unfold stained; split
    next hz=> rw [one_mul]
    next hz=>
       apply mul_eq_zero.mpr; right; unfold Activities.gasOccurrence; refine if_neg (fun H=>?_); obtain ⟨j,hj,hb⟩:= Finset.not_disjoint_iff.mp h
       rw [← H.2] at hb; obtain ⟨u,hu,hU⟩:=mem_biUnion.mp hb; exact hz ⟨u,mem_filter.mpr ⟨hu,fun h=>Finset.disjoint_left.mp h ((R.activities.forced u).inventory_sup hU) hj⟩⟩
def pantone (T:Forest S.ratio)(U:Config G f):=Lattice.gauge (T.foldAt U) U
lemma pantone_in (T:Forest S.ratio):Pedal (G:=G) S (pantone T):=by
   intro k hk U; funext i; unfold pantone
   have hz(x): T.foldAt (Lattice.gauge k U) x=T.foldAt U x * (k x)⁻¹:=by unfold Forest.foldAt; rw [travel_gauge,T.hike_root,hk]; group
   rw [funext hz]; unfold Lattice.gauge; group
lemma pantone_self (T:Forest S.ratio) (v:T.Slice G): pantone T (T.drape v)=T.drape v:=by
   have h0(u:Walk)(x:Site f):travel (1:Config G f) x u=1:=by induction u generalizing x; rfl; next d u ih=> rw [travel,ih,mul_one]; unfold Step.read; split <;> simp
   have hp : T.foldAt (T.drape v)=T.foldAt (1:Config G f):= T.names (T.drape v) _ fun j hj=> T.on_tree v ⟨j,hj⟩
   unfold pantone; rw [hp]; funext i; simp [Lattice.gauge,Forest.foldAt,h0]
def walksAt (T:Forest S.ratio) (i:Bond f):Support f := (visits i.1 (T.hike i.1)).toFinset ∪ (visits (i.1+step i.2) (T.hike (i.1+step i.2))).toFinset
lemma poses (T:Forest S.ratio)(i:Bond f): LocalOn (walksAt T i) (fun U:Config G f=>pantone T U i):=by
    intro U V h; unfold pantone Lattice.gauge Forest.foldAt; have he(x:Site f):x∈(Lattice.visits x (T.hike x)).toFinset:=by cases T.hike x <;> simp [Lattice.visits]
    dsimp only; rw [h i (mem_union_left _ (he i.1)) (mem_union_right _ (he _)), show travel U i.1 (T.hike i.1) = travel V _ _ from travel_local _ _ U V (agrees_mono h ?_),show travel U (i.1+step i.2) (T.hike _) = travel V (i.1+step i.2) (T.hike (i.1+step i.2)) from travel_local _ _ U V (agrees_mono h ?_)]
    all_goals first| exact fun j hj=> mem_union_left _ (List.mem_toFinset.mpr hj)| exact fun j hj=> mem_union_right _ (List.mem_toFinset.mpr hj)
lemma costPose (T:Forest S.ratio)(i:Bond f):i.1∈walksAt T i ∧ (walksAt T i).card≤8*S.patch.L.val+2:=by
    unfold walksAt; have he(x:Site f)(u:Walk):x∈ Lattice.visits x u ∧ (Lattice.visits x u).length=u.length+1:=by induction u generalizing x; simp [Lattice.visits]; next d u ih=> have hx:=(ih (x+d.vec)).2; simp [Lattice.visits,hx]
    have hx (x:Site f) : (Lattice.visits x (T.hike x)).toFinset.card≤4*S.patch.L.val+1:= le_trans (List.toFinset_card_le _) ((he x _).2.trans_le (Nat.add_le_add_right ((T.hike_lower _).trans (T.bound x)) _))
    exact ⟨mem_union_left _ (List.mem_toFinset.mpr (he ..|>.1)), (card_union_le ..).trans ((Nat.add_le_add (hx _) (hx _)).trans (by omega))⟩
-- bona data BOTH leaves
variable {u:Config G f→ℝ}{Y:Support f}
lemma masking (hs: HasSlots R.p R.activities) (hp : Paced R Y S u w)(hy:Y.Nonempty) : ∃ M:Leaf S R, ∃ i:ℕ, M.turn= .logKey i ∧ M.crest=Y∧ M.ingredient=masked R.p.threshold Y u ∧ M.weight=w:=by
    obtain ⟨o,ho⟩:=hy; let i := Blush.found o Y ho; have hi : (R.activities.reg i).support=Y:= congr_arg RegularAddress.support (Blush.latch R o Y ho hs)
    let P:= Wing.logKey i; have hv:= hp.pedal
    let f:= masked R.p.threshold Y u
    have he:UsesFinal R.p.threshold (P.support R) f:=by
       rw [show P.support R=Y from hi]; intro U V h hF; have hz:=hp.owns U V h hF
       have hh: Healthy R.p.threshold Y U ↔ Healthy R.p.threshold Y V :=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,hF,Finset.disjoint_iff_inter_eq_empty]
       unfold f masked Set.indicator; by_cases hX: Healthy R.p.threshold Y U <;> simp_all
    have hq : Pedal S f:=by
       intro k h U; have he: Healthy R.p.threshold Y (gauge k U) ↔ Healthy R.p.threshold Y U := by unfold Healthy; rw [RG.gauge_flags]
       unfold f masked Set.indicator; simp [he,hv k h U]
    have hb(V): f V≠0→ P.qualifies R V:=by
       change _→ Healthy _ (R.activities.reg i).support _; rw [hi]; exact fun h=> by_contra fun hv=> h (masked_ne _ _ _ _ hv)
    have hf (u'): ‖f u'‖ ≤ w:=by unfold f masked Set.indicator; split; exact hp.bound _; simp only [norm_zero]; exact (norm_nonneg _).trans (hp.bound u')
    refine ⟨⟨P,f,he,hb,hs.regular _,w,hf,hq,masked_measurable _ _ _ hp.meas⟩,i,rfl,hi,rfl,rfl⟩
lemma stepped (hp : Paced R Y S u w) : Paced R Y S (fun U=> if Healthy R.p.threshold Y U then 0 else u U) w:=by
   refine ⟨?_,Measurable.ite ((healthy_closed ..).measurableSet) measurable_const hp.meas, ?_,fun U=>?_⟩
   · intro U V h hF; have hz:=hp.owns U V h hF; simp_rw [hz, show Healthy R.p.threshold Y U ↔ Healthy R.p.threshold Y V from (by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,hF,Finset.disjoint_iff_inter_eq_empty])]
   · intro k h U; simp_rw [Healthy,RG.gauge_flags,hp.pedal k h U]; split_ifs <;> rfl
   split_ifs
   · exact (norm_zero.trans_le ((norm_nonneg _).trans (hp.bound U)))
   exact hp.bound U
end YM.PhysicalNext.Repeat.Aroma
