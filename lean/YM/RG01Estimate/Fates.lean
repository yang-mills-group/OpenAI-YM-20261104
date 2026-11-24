import YM.RG01Estimate.Passport
import YM.RG01Estimate.VacuumListing
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young

/-!
# Partition after re-pricing. Identical on the full physical polynomial (vacuum)

Important: the `showcase` for the RG03 transfer is not just defined by the
price failing to exceed some threshold. It's a simple geometry criterion for
currents that can appear on different periods if the underlying path, relative
budgets etc. live there. Remaining cost inside city still to be proved. Hypotheses
about the same path/analytic packets across periods belong to that re-expression.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Fate

open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim
open Next.Scheduling
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ s a α : ℝ} {j n : ℕ} {χ : Chi}
    {H : Cash W s μ L Q o α T R} (E : Set ℕ)

-- exports
abbrev high (z : H.fragrances) (p : ℕ) := p ≤ Height.degree H z ∨ 1 ≤ Height.overlap H z ∨ (Pressure.Stores.till s:ℝ) ≤ Height.depth H z
def inherits (z : H.fragrances) := ∃ i∈E, z=Brim.icon H i

def arc (_H : Cash W s μ L Q o α T R) (D : ℕ) (p : Head S) : Prop :=
    p.elim (fun _=>False) (Sum.elim (fun _=>False) (Sum.elim
      (Sum.elim (Sum.elim (fun i=> i∉E) (Sum.elim (fun i=> Raw.atomCharge R.path.cubic i ≤ D)
        (Sum.elim (fun i=> Raw.atomCharge R.path.quartic i ≤ D) (Sum.elim (fun i=> Raw.atomCharge R.path.loop i ≤ D)
          (fun _=>False))))) (Sum.elim (fun _=>True) (fun _=>False)))
      (fun _=>False)))
structure showcase (p : ℕ) (z : H.fragrances) : Prop where
  possible : coefficient H.seam z.2 ≠ 0
  rows : z.fst+1 < p
  alive i : Ac.Spark H.supportP (z.2 i).val
  limited i : (z.2 i).val.card < p
  driver (i) (x : Head S) : x∈(z.2 i).val → arc E H (radiusB s) x

lemma disjoint (z : H.fragrances) (p : ℕ) (h : inherits E z) : ¬ showcase E p z := by
  rintro H
  obtain ⟨i,hi,rfl⟩:= h
  exact (H.driver none (Opacity.key S i) (Finset.mem_singleton_self _)) hi

-- payout tests
lemma rich (z : H.fragrances) (p : ℕ) (hd : 1 ≤ grow G L s) (he : grow G L s^p ≤ Real.exp (Q.mark L μ s))
    (hu : grow G L s^p ≤ Real.exp (Q.ε*Pressure.Stores.till s)) (hz : high z p) : grow G L s^p ≤ beacon H z := by
  have hg:0≤ grow G L s:=zero_le_one.trans hd
  have hO : 0 ≤ Q.mark L μ s:= H.laws.acquired.marked
  have hT : 1≤Real.exp (Q.mark L μ s*overlap H z):= Real.one_le_exp (mul_nonneg hO (Nat.cast_nonneg _))
  have hA : 1≤ Real.exp (Q.ε*depth H z):= Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun _ _=> H.positive_volume _))
  rcases hz with h|h|h
  · exact ((pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (pow_nonneg hg _) hT).trans
        (le_mul_of_one_le_right (mul_nonneg (pow_nonneg hg _) (Real.exp_pos _).le) hA)))
  · exact he.trans ((Real.exp_monotone (le_mul_of_one_le_right hO (show (1:ℝ) ≤ overlap H z from by exact_mod_cast h))).trans
      ((le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans
        (le_mul_of_one_le_right (mul_nonneg (pow_nonneg hg _) (Real.exp_pos _).le) hA)))
  exact hu.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans (le_mul_of_one_le_left (Real.exp_pos _).le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hT)))

section
variable (Z : Alphabet c f→ℝ) {D : ℝ}
lemma toll_ge (hx : 1≤D) (hz : ∀ i,1 ≤ Z i) (p : Head S) : 1 ≤ Expense.toll Z D p := by
  rcases p with i|i; exact le_rfl
  exact one_le_mul_of_one_le_of_one_le hx (hz i)
private lemma promote {ι : Type} (g:ι→ℝ) {s:Finset ι} (p : ∀ i∈s,1≤g i) {x:ι} (hx:x∈s) : g x ≤ ∏ i∈s,g i := by
  rw [← Finset.mul_prod_erase _ _ hx]; exact le_mul_of_one_le_right (zero_le_one.trans (p x hx))
    (Finset.one_le_prod (fun i hi=> p i (Finset.mem_of_mem_erase hi)))
lemma each (hx : 1≤D) (hz : ∀ i,1 ≤ Z i) (u : H.fragrances) (j : Option (Fin u.fst)) (x : Head S)
    (hp : x∈(u.2 j).val) : Expense.toll Z D x ≤ clusterCost Z D u :=
  le_trans (promote (g:=Expense.toll Z D) (fun i _=>toll_ge Z hx hz i) hp) (promote
    (g:=fun j=> sumT Z D (u.2 j).val) (fun _j _=> Finset.one_le_prod (fun i _=> toll_ge Z hx hz i)) (mem_univ j)) -- names
lemma multiplied (hx : 1 ≤ D) (hz : ∀ i,1 ≤ Z i) (u : H.fragrances) (j : Option (Fin u.fst)) (x : Alphabet c f)
    (he : (Sum.inr x) ∈ (u.2 j).val) (hr : ∀ j, (u.2 j).val.toLeft=∅) :
    D^Height.breadth H u * Z x ≤ clusterCost Z D u := by
  let f (t:Head S) := Expense.toll Z (1:ℝ) t
  have hu j : sumT Z D (u.2 j).val=(D^(u.2 j).val.card)*(sumT Z (1:ℝ) (u.2 j).val) := by
    calc
      _ = ∏ i ∈ (u.2 j).val,D*f i := Finset.prod_congr rfl fun i hi=> by
        rcases i with i|i
        · have hx:= Finset.mem_toLeft.mpr hi; rw [hr j] at hx; simp at hx
        unfold Expense.toll f Expense.toll; simp
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
                  rfl
  unfold clusterCost; simp_rw [hu]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have hp:= each Z (D:=1) (by rfl) hz u j (.inr x) he
  unfold Expense.toll at hp; simp only [Sum.elim,one_mul] at hp
  exact mul_le_mul_of_nonneg_left hp (pow_nonneg (zero_le_one.trans hx) _)
end

lemma extra_le {z : H.fragrances} (i:Option (Fin z.fst)) {x : LogLetter c f}
    (hx : (Sum.inr (Sum.inr (Sum.inl (Sum.inl x))))∈(z.2 i).val) : (Raw.extra T R x:ℝ) ≤ depth H z := by
  apply le_trans (b:=H.shapeW (z.2 i).val) _ (single_le_sum (f:=fun i=> H.shapeW (z.2 i).val)
    (fun i _=> H.positive_volume _) (mem_univ i))
  let Y : Head S := Sum.inr (Sum.inr (Sum.inl (Sum.inl x)))
  apply le_trans _ (Finset.single_le_sum _ (show Y∈(z.2 i).val from hx))
  swap
  · rintro (y|y) _
    · exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _))
    exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

/-- The only uncharged log components are the advertised model portion,
zeros, and the small-support inherited-e case that needs derivative contraction.
Assumes separately that E's complement was rendered as the desired analytic
patterns. That input assumption enters the Taylor estimate, not this bound. -/
theorem covered (z : H.fragrances) (V : Config G c) (h : March.stream H χ V z≠0) (p : ℕ) (hp : 0<p) (hd : ¬high z p)
    (hq : ¬ inherits E z) (hu : ¬ showcase E p z) {x y D : ℝ} (hx : 1≤x) (hy : 1≤y) (hD : 1≤ D) (hM : D*x ≤ y) :
    D^2*x ≤ clusterCost (weigh c f E x y) D z := by
  have hl : depth H z < Pressure.Stores.till s:= lt_of_not_ge (fun h=>hd (Or.inr (Or.inr h)))
  have he : ¬ VacuumCensus.tail H p z := by
    rintro (h|h|h)
    · exact hd (Or.inl h)
    · exact hd (Or.inr (Or.inl h))
    have hv : (Pressure.Stores.till s:ℝ) ≤ (p:ℝ)*Pressure.Stores.till s := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hp)
    exact hl.not_ge (hv.trans h)
  obtain ⟨_,hk,hr,hL⟩:= VacuumCensus.seed_free z V h he
  have ht (i: Option (Fin z.fst)) := (hL i).1
  have hv : coefficient H.seam z.2 ≠0 := fun hp=> h (by unfold stream Gas.term; rw [hp,zero_mul,zero_div])
  obtain ⟨i,y',hi,hc⟩ : ∃ i y', y'∈ (z.2 i).val ∧ ¬arc E H (radiusB s) y' := by
    by_contra! h; exact hu ⟨hv,hr,ht,fun i=>(hL i).2.2.1,h⟩
  have hz' := each (weigh c f E x y) hD (ones E hx hy) z i y' hi
  have hz : D^2*x ≤ D*y := by rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_left hM (zero_le_one.trans hD)
  rcases y' with l|l
  · have hp:= Finset.mem_toLeft.mpr hi; rw [(hL i).2.2.2.1] at hp; simp at hp
  rcases l with l|l|l
  · have hp : l∈Matter.own (z.2 i).val:= Finset.mem_toLeft.mpr (Finset.mem_toRight.mpr hi)
    rw [(hL i).2.2.2.2] at hp; simp at hp
  swap; · exact hz.trans hz'
  rcases l with l|l|l
  · have hh: Raw.extra T R l ≤ radiusB s := Nat.cast_le (α:=ℝ)|>.1 ((extra_le _ hi).trans
      (hl.le.trans (by exact_mod_cast show Pressure.Stores.till s ≤ radiusB s from Nat.div_le_self ..)))
    rcases l with l|l|l|l|l
    · have ha l':1 ≤ (z.2 l').val.card:= Finset.card_pos.mpr (ht l').1
      have hp : l∈ E:= Classical.byContradiction hc
      have ht : 2 ≤ Height.breadth H z := by
        by_contra! h; exact hq ⟨l,hp, Beam.lantern z ha (by omega) i hi⟩
      have hk:= multiplied (weigh c f E x y) hD (ones E hx hy) z i (Sum.inr (Sum.inl (.inl (.inl l)))) hi (fun i=>(hL i).2.2.2.1)
      simp only [Reprice.weigh, rays, Inherit.weight,Inherit.sees,Sum.elim,hp,↓reduceIte] at hk
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD ht) (zero_le_one.trans hx)).trans hk
    · exact (hc hh).elim
    · exact (hc hh).elim
    · exact (hc hh).elim
    rcases l with l|l <;> exact hz.trans hz'
  · exact (hc trivial).elim
  exact hz.trans hz'

lemma cover_inherited (H : Cash W s μ L Q o α T R) (i : ℕ) {p : ℕ} (h : ¬ high (Brim.icon H i) p) :
    coverNumber (radiusB s) (Brim.plate H i).support ≤ radiusB s := by
  rw [← Brim.concern H i]
  apply Beam.shall; rintro (ht|ht)
  · unfold degree Height.acme Height.breadth icon once at ht
    simp [Height.pins,Brim.head,Opacity.key,Silica.horn,Silica.Clutch.teeth,extraA] at ht
  exact h (Or.inr ht)

end YM.RG01Estimate.Fate
