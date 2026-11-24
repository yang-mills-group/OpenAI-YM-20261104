import YM.LocalLTE.E6.Profit
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Oriole
/-! Beyond arbitrary LTE letter count, true survivors; no inherited calls in the universal Kin sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Brim Greenbelt
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}

structure Elder (ℓ:ℕ) (p : H.ThinP) : Prop where
  connects : Ac.Spark H.supportP p.val
  unforced : p.val.toLeft = ∅
  noK : own p.val = ∅
  nonempty : 1 ≤ p.val.card
  few : p.val.card≤ ℓ
  pays : H.shapeW p.val ≤ radiusB s

lemma aging {z:H.fragrances}{V:Config G c} (hv:stream H χ V z≠0) (he : ¬tiredN H ℓ z):
    (∀ i,Elder ℓ (z.2 i)) ∧ z.1< ℓ:= by
  have hL i : leaflet H χ V (z.2 i)≠0:=fun h=> hv (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) h,mul_zero,zero_div])
  have hp' (p:H.ThinP) (hx:leaflet H χ V p≠0) : Ac.Spark H.supportP p.val∧ troupe T R Q.halo (radiusB s) p.val := by
    by_contra he; apply hx; unfold leaflet likely; simp_rw [vacuity V p he,sum_const_zero,mul_zero]
  have hz i:= hp' _ (hL i)
  obtain ⟨hp,hr,hd⟩:= (and_congr Iff.rfl not_or|>.1 (not_or.mp he))
  have ht := lt_of_not_ge hp
  have he : breadth H z < ℓ := lt_of_le_of_lt (Nat.le_add_left ..) ht
  constructor
  · intro i; let k: H.ThinP:=z.2 i
    obtain ⟨hs,hh⟩:= hz i
    have hu : Cash.numP k.val <1:= lt_of_le_of_lt (single_le_sum (s:=univ) (f:=fun j=> Cash.numP (z.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge hr)
    have hF:k.val.toLeft=∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨w,hw⟩=> by
      have hx : 1 ≤ w.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hh.1.checkpoints w hw).1
      exact (Nat.not_lt.mpr (hx.trans (show w.shares≤Cash.numP k.val from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hw)))) hu
    refine ⟨hs,hF,Finset.not_nonempty_iff_eq_empty.mp ?_,Finset.card_pos.mpr hs.1,(single_le_sum (f:=fun j=> (z.2 j).val.card) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans he.le,?_⟩
    · rintro ⟨t,ht⟩; obtain ⟨j,hj⟩ := (R.activities.forced t).inventory_ne; obtain ⟨l,hy,hv⟩:=hh.2.2 _ ht _ hj
      unfold roster Packets.store at hy; change (z.2 i).val.toLeft= _ at hF; rw [hF] at hy; simp at hy
    exact le_trans (single_le_sum (f:=fun i=>H.shapeW (z.2 i).val) (fun i _=> H.positive_volume _) (mem_univ i)) ((lt_of_not_ge hd).le.trans (by exact_mod_cast Nat.div_le_self ..))
  exact lt_of_lt_of_le (Nat.lt_succ_self z.1) ((Beam.on_one z (fun i=>Finset.card_pos.mpr (hz i|>.1.1))).trans he.le)

def ancestry (z:H.fragrances):Prop:= ∃ i p, Opacity.key S p ∈ (z.2 i).val
lemma secular {z:H.fragrances}{V:Config G c} (hv:stream H χ V z≠0) (he : ¬ tiredN H ℓ z)
    (hx : ¬ancestry z) (i) (u) (hh : u∈ (z.2 i).val): Beam.Pennies S u := by
  have h:=(aging hv he).1 i; have ht:= lt_of_not_ge (not_or.mp he).1
  rcases u with u|u
  · have hz:= mem_toLeft.mpr hh; rw [h.unforced] at hz; exact (notMem_empty _ hz).elim
  have hz : Silica.hornN ℓ u ≤ acmeN H ℓ z := by
    exact (le_trans (b:=pinsN ℓ S (z.2 i).val) (single_le_sum (f:=Sum.elim _ _) (fun _ _=>Nat.zero_le _) hh) (single_le_sum (f:=fun j=> pinsN ℓ S (z.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i)))
  unfold degreeN at ht
  have hg : hornN ℓ u < ℓ := by omega
  rcases u with u|u|u
  · have ht : u∈own (z.2 i).val := mem_toLeft.mpr (mem_toRight.mpr hh); rw [h.noK] at ht; exact (notMem_empty _ ht).elim
  · refine ⟨u,rfl,?_⟩; rcases u with u|u|u
    · rcases u with u|u|u|u|u|u
      · exact hx ⟨_,_, show Opacity.key S u∈(z.2 i).val from hh⟩
      · trivial
      · trivial
      · trivial
      all_goals exfalso; change ℓ+2<ℓ at hg; omega
    · trivial
    exfalso; change ℓ+2<ℓ at hg; omega
  exfalso; change ℓ+2<ℓ at hg; omega

lemma atHeir (he : ∀ i U,R.activities.E i U=0) {z:H.fragrances} (hz:ancestry z) (x: Config G c): stream H χ x z=0:= by
  obtain ⟨i,p,hp⟩:= hz; let K:=z.2 i
  unfold stream Gas.term; suffices hk: leaflet H χ x K=0 by rw [prod_eq_zero (Finset.mem_univ i) hk,mul_zero,zero_div]
  have he i U : R.activities.regularOccurrence R.p i U=0 := by simp [Activities.regularOccurrence,masked,Set.indicator, he]
  unfold March.leaflet Pond.likely Stained.fringe
  have hx (F:Tree.Forest S.ratio) (Y:Coat T F) J u : Polar.floating Y o.a R W Q.table u J Q.halo K.val=0 := by
    unfold Polar.floating; apply Finset.prod_eq_zero hp
    change Real.exp (-(R.activities.regularOccurrence _ p _) * _) -1= _; rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
  have hv (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y W o.a K.val R Q.table Q.halo=0 := by
    unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hx,mul_zero,integral_zero,sum_const_zero]
    rfl
  change _ * ∑ y: Greenbelt.Reserve S, (∫ v, Shield.shelter _ _ _ K.val _ _ _ ∂ _) = _; simp only [hv,integral_zero,sum_const_zero,mul_zero]
lemma heir_priced {z:H.fragrances} (hz:ancestry z) {x:Config G c} (hv: stream H χ x z≠0) : Beam.lit H z:= by
  by_contra h
  have hy:= Beam.kids χ z x hv h
  obtain ⟨i,p,hp⟩:= hz
  obtain ⟨l,he,hh⟩:= hy.lives i _ hp
  change Sum.inr (Sum.inr (Sum.inl (Sum.inl (Sum.inl p))))=_ at he; obtain rfl := (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj he)))
  exact hh
end YM.PhysicalNext.Repeat.Height
