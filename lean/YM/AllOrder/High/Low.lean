import YM.AllOrder.High.Officer
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Camp
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Wing

/-!
# Identify every young occurrence after independent cutoff tuning.

Exception: interactions with actual inherited E are precisely identified.
Never infer young-in-reg implies all V tags active. `noLines` reads on the full
unmasked functions, not on masked evaluations. `maturity` includes disappearing
chains even on no-hot-shift configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R} {p : BudgetPoint}
    (χ : Chi)

lemma noKE (u : J.ThinP) (h : troupe T R Q.halo (radiusB s) u.val) (hp : Cash.numP u.val < 1) : u.val.toLeft=∅ ∧ own u.val=∅ := by
  have he : u.val.toLeft=∅:= Finset.not_nonempty_iff_eq_empty.mp fun ⟨i,hi⟩=> by
    have hx : 1 ≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (h.1.checkpoints i hi).1
    exact (Nat.not_lt.mpr (hx.trans (show i.shares≤Cash.numP u.val from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi)))) hp
  refine ⟨he,Finset.not_nonempty_iff_eq_empty.mp ?_⟩; rintro ⟨i,hi⟩; obtain ⟨j,hj⟩ := (R.activities.forced i).inventory_ne; obtain ⟨z,hy,hv⟩:=h.2.2 _ hi _ hj; unfold roster Packets.store at hy; rw [he] at hy; simp at hy

def inheritKey (S : StepData c f) (i: Head S) := ∃ k:ℕ, Opacity.key S k=i
lemma children (u : J.fragrances) (h : ¬tiredV J k u) (V : Config G c) (hp : stream J χ V u≠0) : u.1<k ∧ depth J u<Pressure.Stores.till s ∧ ∀ i,
    Ac.Spark J.supportP (u.2 i).val ∧ (u.2 i).val.card≤k ∧ ∀ p∈(u.2 i).val, Beam.Pennies S p ∨ inheritKey S p := by
  obtain ⟨he,hM,hV⟩:= (and_congr Iff.rfl not_or|>.1 (not_or.mp h))
  have hs: degreeP J k u < k := lt_of_not_ge he; have hy : breadth J u < k := (Nat.le_add_left ..).trans_lt hs
  have hh i : leaflet J χ V (u.2 i) ≠ 0:= fun h=> hp (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) h,mul_zero,zero_div])
  have hQ i : Ac.Spark J.supportP (u.2 i).val ∧ troupe T R Q.halo (radiusB s) (u.2 i).val := by
    by_contra h; apply hh i; unfold leaflet likely; simp_rw [vacuity V (u.2 i) h,sum_const_zero,mul_zero]
  have hU := Beam.on_one u (fun i=> Finset.card_pos.mpr (hQ i).1.1)
  refine ⟨by omega,lt_of_not_ge hV,fun i=> ⟨(hQ i).1, ((single_le_sum (f:=fun j=> (u.2 j).val.card) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans hy.le),fun p hp=> ?_⟩⟩
  obtain ⟨hA,hB⟩:= noKE _ (hQ i).2 (lt_of_le_of_lt (single_le_sum (f:=fun j=> Cash.numP (u.2 j).val) (fun i _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge hM))
  rcases p with z|z
  · have h:= mem_toLeft.mpr hp; rw [hA] at h; exact (notMem_empty _ h).elim
  have ht : Silica.spike k z< k:=
    (le_trans (b:= Height.cardP J k u) (le_trans (b:=prongs k S (u.2 i).val) (single_le_sum (f:=Sum.elim (fun _ : Stores S => 0) (Silica.spike (c:=c) (f:=f) k)) (fun _ _=> Nat.zero_le _) hp) (single_le_sum (f:=fun j=>prongs k S (u.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i))) (Nat.le_add_right ..)).trans_lt hs
  rcases z with z|z|z
  · have h : z∈own (u.2 i).val := mem_toLeft.mpr (mem_toRight.mpr hp); rw [hB] at h; exact (notMem_empty _ h).elim
  swap
  · exact (lt_irrefl k ht).elim
  by_cases he:inheritKey S (.inr (.inr (.inl z))); · exact Or.inr he
  refine Or.inl ⟨z,rfl,?_⟩
  rcases z with z|z|z
  · rcases z with z|z|z|z|z|z
    · exact he ⟨z,rfl⟩
    · trivial
    · trivial
    · trivial
    all_goals exact (lt_irrefl k ht).elim
  · trivial
  exact (lt_irrefl k ht).elim
lemma noLines (u : J.fragrances) (i : _) (j:ℕ) (hp : Opacity.key S j ∈ (u.2 i).val) (he : R.activities.E j=0) : (fun V:Config G c => stream J χ V u)=0 := by
  have he U: R.activities.regularOccurrence R.p j U=0:= by simp_rw [Activities.regularOccurrence,masked, he]; unfold Set.indicator; split<;> rfl
  have hz (F:Tree.Forest S.ratio) (Y:Coat T F) J z : Polar.floating Y o.a R W Q.table z J Q.halo (u.2 i).val=0:= by
    unfold Polar.floating; refine Finset.prod_eq_zero hp ?_; change Real.exp (-(R.activities.regularOccurrence _ j _) * _) -1= _; rw [he, neg_zero,zero_mul,Real.exp_zero,sub_self]
  have hV (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y W o.a (u.2 i).val R Q.table Q.halo=0:= by
    unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hz,mul_zero,integral_zero,sum_const_zero]
    rfl
  funext U; have hv: leaflet J χ U (u.2 i)=0:= by unfold leaflet likely Stained.fringe; simp_rw [hV,integral_zero,sum_const_zero,mul_zero]
  change stream J χ U u=0; unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) hv,mul_zero,zero_div]
end YM.PhysicalNext.Repeat.Height
