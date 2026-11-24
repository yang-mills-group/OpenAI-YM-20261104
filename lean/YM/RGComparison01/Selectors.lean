import YM.RGComparison01.Bank
import YM.RGComparison01.Survivors
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young

/-!
# Low survivors with long gauges paid

 This version knows native profile/ratio warnings paid jointly with
 breadth. E contributions survive iff they read *none* of the
 distinguished E inputs of the `Weeds` tests. It does NOT compare E
 of distinct histories. Use hRegs from the rendering debt at RG03.
 Distinct seed stores first; coupling-flat budgets in caller. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open PhysicalNext PhysicalNext.Repeat Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

namespace Selector
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ s α : ℝ}
    {χ : Chi} {H : Cash W s μ L Q o α T R} {z : H.fragrances} {ℓ : ℕ}

/-- Use before testing unmasked payload. NB doesn’t chase path units. -/
def JOB (S : StepData c f) (i : Head S) := ∀ (V : ℕ → ℝ) (t : ℝ), Sail.policyP V t i=t

def Weeds (ℓ : ℕ) (z : H.fragrances) : Prop :=
    ℓ ≤ Height.degree H z ∨ 1 ≤ Height.overlap H z ∨ (radiusB s:ℝ) ≤ Height.depth H z ∨
      ∃ i j, j∈ (z.2 i).val ∧ JOB S j

def Inherited (Ω : ℕ→Prop) (z : H.fragrances) : Prop :=
    ∃ i, Ω i ∧ ∃ j, Opacity.key S i ∈ (z.2 j).val

lemma ups_component {p : Head S} {V : ℕ → ℝ} {t : ℝ} (ht : 1 ≤ t) (hV : ∀ i, 1 ≤ V i)
    (j : Option (Fin z.fst)) (hj : p∈ (z.2 j).val) : Sail.policyP V t p ≤ Beacon.ups V t z := by
  have hw {I:Type} [DecidableEq I] (f : I→ℝ) (Z : Finset I) (hf : ∀ i,1≤f i)
      (i:I) (hi : i∈Z) : f i ≤ (∏ v∈Z,f v) := by
    rw [← Finset.prod_singleton f]; exact Finset.prod_le_prod_of_subset_of_one_le
      (Finset.singleton_subset_iff.mpr hi) (fun _ _=>zero_le_one.trans (hf _)) (fun _ _ _=> hf _)
  exact (hw _ _ (Sail.policy_ge V t ht hV) _ hj).trans (hw (fun i => ∏ v∈ (z.2 i).val,Sail.policyP V t v)
    univ (fun i=> one_le_prod fun v _=> Sail.policy_ge V t ht hV v) j (mem_univ j))


open Beacon
local notation "gZ" => Height.grow G L s

lemma weeds_pay (V : ℕ→ℝ) (hV : ∀ i, 1 ≤ V i) (t : ℝ) (ht : 1 ≤ t) (hd : 1 ≤ gZ)
    (hL : gZ ^ ℓ ≤ t)
    (hseed : gZ ^ ℓ ≤ Real.exp (Q.mark L μ s))
    (hlong : gZ ^ ℓ ≤ Real.exp (Q.ε * radiusB s))
    (z : H.fragrances) (h : Weeds ℓ z) : gZ ^ ℓ ≤ Beacon.spire V t z := by
  have hp := one_le_pow₀ (n:=Height.degree H z) hd
  have hmark : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have h_ov : 1 ≤ Real.exp (Q.mark L μ s * Height.overlap H z) :=
    Real.one_le_exp (mul_nonneg hmark (Nat.cast_nonneg _))
  have h_depth : 1 ≤ Real.exp (Q.ε * Height.depth H z) :=
    Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun _ _ => H.positive_volume _))
  rcases h with h|h|h|⟨j,i,hh,he⟩
  · apply le_trans _ (higher hd V t ht hV z)
    exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (zero_le_one.trans hp) h_ov).trans
      (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hp h_ov)) h_depth))
  · apply le_trans _ (higher hd V t ht hV z)
    exact hseed.trans ((Real.exp_monotone (le_mul_of_one_le_right hmark (show (1:ℝ) ≤ Height.overlap H z by exact_mod_cast h))).trans
      ((le_mul_of_one_le_left (zero_le_one.trans h_ov) hp).trans
        (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hp h_ov)) h_depth)))
  · apply le_trans _ (higher hd V t ht hV z)
    apply (hlong.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le))).trans
    exact le_mul_of_one_le_left (zero_le_one.trans h_depth) (one_le_mul_of_one_le_of_one_le hp h_ov)
  have hv := ups_component ht hV j hh; rw [he] at hv
  exact hL.trans ((hv : t ≤ Beacon.ups V t z).trans (le_mul_of_one_le_right
    ((zero_le_one.trans ht).trans hv) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp h_ov) h_depth)))

lemma bounty {u : ℝ} {Ω : ℕ→Prop} (hu : 1 ≤ u) (ht : Inherited Ω z) (t : ℝ) (hx : 1 ≤ t) :
    u ≤ Beacon.ups (Tithe.bonus Ω u) t z := by
  obtain ⟨j,hj,i,hi⟩:=ht
  have hv:= ups_component hx (Tithe.bonus_ge Ω hu) i hi
  rw [show Sail.policyP (Tithe.bonus Ω u) t (Opacity.key S j)= u from (if_pos hj : Tithe.bonus Ω u j=u)] at hv
  exact hv
lemma minor_inherited {Ω : ℕ→Prop} (h:Inherited Ω z) (hz : ¬ Height.tired H z) (V : Config G c)
    (hV : Blaze.March.stream H χ V z ≠ 0) : ∃ i,Ω i ∧ z= Brim.icon H i := by
  obtain ⟨i,hh,q,hq⟩:=h
  have ht:= novices χ z V hV hz; have hs j:= ht.enter.2.2 j; have hy := ht.arity
  have ha: 1 ≤ Height.acme H z:= by
    apply le_trans (b:=Height.pins S _)
    swap; · exact single_le_sum (f:=fun p=> pins S (z.2 p).val) (fun i _=> Nat.zero_le _) (mem_univ q)
    exact show Sum.elim _ Silica.horn (Opacity.key S i) ≤_ from single_le_sum (f:=Sum.elim (fun _:Stores S=>0) Silica.horn) (fun _ _=> Nat.zero_le _) hq
  unfold degree at hy
  exact ⟨i,hh,Beam.lantern z (fun j=> (hs j).shares.1) (by omega) q hq⟩

section low
lemma sound_kind {B : ℕ→Prop} (he : ¬Inherited B z) {x : Head S} {i}
    (hx : x∈ (z.2 i).val) (hX : ¬ JOB S x) (ht : (z.2 i).val.toLeft=∅) (hz : own (z.2 i).val=∅) :
    (∃ p, ¬ B p ∧ x=Opacity.key S p) ∨ Beam.Pennies S x := by
  rcases x with x|x
  · have he := mem_toLeft.mpr hx; rw [ht] at he; exact (notMem_empty _ he).elim
  rcases x with x|x|x
  · have he : x∈own (z.2 i).val := mem_toLeft.mpr (mem_toRight.mpr hx); rw [hz] at he; exact (notMem_empty _ he).elim
  · rcases x with x|x|x
    · rcases x with x|x|x|x|x
      · exact Or.inl ⟨x,fun h=> he ⟨x,h,i,hx⟩,rfl⟩
      · exact Or.inr ⟨_,rfl,True.intro⟩
      · exact Or.inr ⟨_,rfl,True.intro⟩
      · exact Or.inr ⟨_,rfl,True.intro⟩
      exact (hX fun V t=>rfl).elim
    · exact Or.inr ⟨_,rfl,True.intro⟩
    exact (hX fun V t=>rfl).elim
  exact (hX fun V t=>rfl).elim

open Finset in
lemma left_low (Ω : ℕ→Prop) (h : ¬Weeds ℓ z) (hx : ¬Inherited Ω z) (V : Config G c) (hz : stream H χ V z ≠ 0) :
    z.1 + 1 < ℓ ∧ Height.breadth H z < ℓ ∧ Height.depth H z < radiusB s ∧
    (coverNumber (radiusB s) (Captain.reachability (H:=H) z)) < radiusB s ∧
    ∀ i : Option (Fin z.fst), Ac.Spark H.supportP (z.2 i).val ∧
      ∀ p ∈ (z.2 i).val,(∃ j,¬Ω j ∧ p=Opacity.key S j) ∨ Beam.Pennies S p := by
  have hh := not_or.mp h; have hu := not_or.mp hh.2; have hy:= not_or.mp hu.2
  have hv j : leaflet H χ V (z.2 j)≠0 := fun h=> hz (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ j) h,mul_zero,zero_div])
  have hp j : Ac.Spark H.supportP (z.2 j).val ∧ troupe T R Q.halo (radiusB s) (z.2 j).val := by
    by_contra h; apply hv j; unfold leaflet likely; simp_rw [Height.vacuity V _ h,sum_const_zero,mul_zero]
  have hℓ: Height.breadth H z < ℓ:=lt_of_le_of_lt (Nat.le_add_left ..) (lt_of_not_ge hh.1)
  refine ⟨lt_of_le_of_lt (Beam.on_one z (fun i=> Finset.card_pos.mpr (hp i).1.1)) hℓ,hℓ,lt_of_not_ge hy.1, ?_,?_⟩
  · suffices hm : (coverNumber (radiusB s) (Captain.reachability (H:=H) z):ℝ) < radiusB s by exact_mod_cast hm
    apply lt_of_le_of_lt _ (lt_of_not_ge hy.1); unfold Height.depth
    apply le_trans ?_ (sum_le_sum (s:=univ) (fun i _=> Survivors.shape_covers (hp i).1))
    have hpos := connected_pay H.seam H.smallAt (radiusB s) H.testS z.2 zero_le_one (by
      intro h; apply hz; unfold stream Gas.term; rw [h,zero_mul,zero_div])
    unfold Trees.currency at hpos; simp_rw [one_mul,← Real.exp_sum, Real.exp_le_exp] at hpos
    exact hpos
  intro i; refine ⟨(hp i).1,?_⟩
  obtain ⟨ht,hk⟩ := Survivors.noSeed (z.2 i) (hp i).2
    (lt_of_le_of_lt (single_le_sum (f:=fun j=> Cash.numP (z.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge hu.1))
  exact fun p hv=> sound_kind hx hv (fun H=>hy.2 ⟨i,p,hv,H⟩) ht hk
end low
end Selector
end YM.RGComparison01
