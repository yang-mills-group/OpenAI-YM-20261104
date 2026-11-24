import YM.RG01.Beacon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Tryouts

/-!
# The grading cut and its survivors in the genuine unforced calculation

The occurrence count is before forming *either* of the two polymer gases
(sum over the list including self-repetitions at the second log).
The long-word cut here is at a multiple of the E-construction cut for ease of
buying arbitrary powers on its existing schedule; don't use same-size holonomy
charts on the resulting survivors without analysis. Include mandatory packets
separately even at short range; `seeded` is a test on occurrence data, not a
function of the field that we'd need to differentiate. All indicators still
retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open Stained Shield
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ} {k j : ℕ}
    {χ : Chi}

variable (H : Cash W s μ L Q o α T R)
def seeded (z : H.fragrances) : Prop := 1 ≤ overlap H z
/-- Remove these from the unforced *log portion* before the small-arity Taylor
analysis. This is NOT yet all the exceptional and high-valuation terms: in
particular long *chains* / analytic-kernel tails of low degree, numerical window
errors, profile events etc may still require exceptional payment. -/
def Cull (K : ℕ) (z : H.fragrances) : Prop :=
  K ≤ Height.degree H z ∨
    K * (Pressure.Stores.till s:ℝ) ≤ depth H z ∨
      seeded H z
variable {H}

lemma seed_le_beacon (hd : 1 ≤ grow G L s) {z : H.fragrances} (hseed : seeded H z) :
    Real.exp (Q.mark L μ s) ≤ beacon H z := by
  have hPos : 1 ≤ Real.exp (Q.ε * depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
    (sum_nonneg fun _ _=> H.positive_volume _))
  have ht : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have hM : 1 ≤ Real.exp (Q.mark L μ s * overlap H z) := Real.one_le_exp (mul_nonneg ht
    (Nat.cast_nonneg _))
  have he : (1:ℝ) ≤ overlap H z := Nat.one_le_cast.mpr hseed -- check
  apply (Real.exp_monotone (le_mul_of_one_le_right ht he)).trans
  exact (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans
    (le_mul_of_one_le_right (mul_nonneg (le_trans zero_le_one (one_le_pow₀ hd)) (le_trans zero_le_one hM)) hPos)

lemma depth_le_beacon (hd : 1 ≤ grow G L s) (z : H.fragrances) :
    Real.exp (Q.ε*depth H z) ≤ beacon H z := by
  have ht : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have hM : 1 ≤ Real.exp (Q.mark L μ s * overlap H z) := Real.one_le_exp (mul_nonneg ht
    (Nat.cast_nonneg _))
  exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hM)

lemma cull_gain (hd : 1 ≤ grow G L s)
    (hdepth : grow G L s ^ 3 ≤ Real.exp (Q.ε*Pressure.Stores.till s)) (K : ℕ)
    (hseed : grow G L s ^ K ≤ Real.exp (Q.mark L μ s)) {z:H.fragrances}
    (h : Cull H K z) : grow G L s ^ K ≤ beacon H z := by
  rcases h with h|h|h
  · exact (pow_le_pow_right₀ hd h).trans (grade_le_beacon hd _)
  · apply le_trans (b:=Real.exp (Q.ε * (K * (Pressure.Stores.till s:ℝ))))
    · rw [mul_left_comm, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (le_trans zero_le_one hd)
        ((le_self_pow₀ hd (by omega : (3:ℕ)≠0)).trans hdepth) _
    exact (Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans (depth_le_beacon hd z)
  exact hseed.trans (seed_le_beacon hd h)

/-- Genuinely the complete genealogy on each occurrence (including self
repetitions). Include detailed premises of the next low-arity test. -/
structure Sparse (J : Cash W s μ L Q o α T R) (K : ℕ) (z : J.fragrances) : Prop where
  short : depth J z < K * (Pressure.Stores.till s:ℝ)
  order : Height.degree J z < K
  nonzero : 1 ≤ Height.degree J z
  count : z.fst + 1 ≤ Height.degree J z
  no_packets : overlap J z=0
  primitive (i : _) : let p: J.ThinP := z.2 i
    Ac.Spark J.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val ∧
      1 ≤ p.val.card ∧ p.val.card ≤ Height.degree J z ∧ p.val.toLeft=∅ ∧ own p.val=∅

lemma survive (z:H.fragrances) {K : ℕ} (h : ¬ Cull H K z) (V)
    (he : stream H χ V z≠0) : Sparse H K z := by
  have hs i : leaflet H χ V (z.2 i) ≠ 0:= fun hz => he (by
    unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) hz,mul_zero,zero_div])
  have hv i : let p:= z.2 i; Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val := by
    by_contra ht
    apply hs i; unfold leaflet likely; simp_rw [Height.vacuity V (z.2 i) ht,sum_const_zero,mul_zero]
  have hi i : 1 ≤ (z.2 i).val.card := Finset.card_pos.mpr ((hv i).1.1)
  have hc : z.fst+1 ≤ breadth H z := by
    refine le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _=>hi i))
    simp
  have hB : breadth H z ≤ Height.degree H z := Nat.le_add_left ..
  have hg := not_or.mp h
  obtain ⟨hd,hx⟩:= not_or.mp hg.2
  have hz : overlap H z=0:= Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (lt_of_not_ge hx))
  refine ⟨lt_of_not_ge hd,lt_of_not_ge hg.1,le_trans (by omega : 1 ≤ z.fst+1) (hc.trans hB),
    hc.trans hB,hz,?_⟩
  intro i p
  have hm : p.val.card ≤ breadth H z := single_le_sum (f:=fun j=> (z.2 j).val.card)
    (fun i _=> Nat.zero_le _) (mem_univ i)
  have hn : Cash.numP p.val < 1:= lt_of_le_of_lt (single_le_sum (f:=fun j=> Cash.numP (z.2 j).val)
      (fun i _=> Nat.zero_le _) (mem_univ i)) (show overlap H z < 1 by rw [hz]; omega)
  have ht : troupe T R Q.halo (radiusB s) p.val := (hv i).2
  have hp : p.val.toLeft=∅:= Finset.not_nonempty_iff_eq_empty.mp fun ⟨a,ha⟩=> by
    have hx : 1 ≤ a.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (ht.1.checkpoints a ha).1
    exact (Nat.not_lt.mpr (hx.trans (show a.shares≤Cash.numP p.val from Finset.single_le_sum
      (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp ha)))) hn
  refine ⟨(hv i).1,ht,hi i,hm.trans hB,hp,Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨l,hl⟩
  obtain ⟨u,hu⟩:= (R.activities.forced l).inventory_ne
  obtain ⟨v,hy,-⟩:= ht.2.2 _ hl _ hu
  unfold roster Packets.store at hy
  rw [hp] at hy
  simp at hy

end YM.RG01.Beacon
