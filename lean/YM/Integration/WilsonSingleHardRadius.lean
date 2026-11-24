import YM.Integration.WilsonOriginalScalarGallery
import YM.Integration.WilsonForcedMarkerLine
import YM.QuadraticLocal.Advent

/-! A stored exceptional singleton on its actual quiet addresses can be heard again
with a larger radius. Keeping its full filed hard program takes care of all old partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Lattice Wilson RG Marker QuadraticLocal Ac
open Push.AbsoluteSums Fusion Fusion.Attached
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {J:Census (Fin 1)} {P:Rep G n} {o:Fin 1→Site n}
variable {T I : Type} {w d a k : ℝ}
local notation "sector" => Hard T P.p P.activities.forced P.activities.K o J

theorem cases (s:J.Mode) : s=J.quiet ∨ s=J.fire 0 := by
  by_cases h:s.val=∅
  · exact Or.inl (Subtype.ext h)
  · obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr h
    right
    apply Subtype.ext
    change s.val={0}
    ext j
    have e:i=0:=Subsingleton.elim _ _
    have e':j=0:=Subsingleton.elim _ _
    subst i
    subst j
    simp [hi]

private theorem price (w:ℝ) (d:ℝ) (pos:0<d) (unit:d≤1) (X:Poly J) :
    Poly.price (fun _=>w/d) X ≤ d⁻¹*Poly.price (fun _=>w) X := by
  unfold Poly.price
  rw [mul_sum]
  apply sum_le_sum
  intro s _
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases cases s with rfl|rfl
  · simpa [Poly.toll,Census.quiet] using one_le_inv₀ pos |>.mpr unit
  · simp [Poly.toll,Census.fire,div_eq_inv_mul]

/-- The same rooted hard catalogue, with its actual quiet addresses, is affordable
at the inverse of its last cost. The field functions are identical. -/
theorem raised (K:sector) (paid:K.Paid (fun _=>w) P.p.B a d)
    (wp:0<w) (pos:0<d) (unit:d≤1) : K.Paid (fun _=>w/d) P.p.B a 1 := by
  obtain ⟨f,covered,bill⟩:=paid.wages
  refine ⟨f,covered,fun y=>?_⟩
  have cap:=budget_scale (inv_nonneg.mpr pos.le) (bill y)
  rw [inv_mul_cancel₀ pos.ne'] at cap
  apply budget_mono cap
  · intro j
    split
    · exact mul_nonneg (Poly.nonnegative (fun _=>div_pos wp pos) _) (Real.exp_pos _).le
    · exact le_rfl
  · intro j
    split
    · next hit =>
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (price w d pos unit _) (Real.exp_pos _).le
    · next miss => rw [mul_zero]

def gallery (K:sector) : Gallery T Empty o P J :=
  ⟨WilsonOriginalScalarGallery.empty P o J T,K⟩

theorem intake (K:sector) (paid:K.Paid (fun _=>w) P.p.B a d) (cap:d≤1) :
    (gallery K).Pays (fun _=>w) a 1 1 := by
  refine ⟨⟨fun j=>j.elim,fun j=>j.elim,fun j=>j.elim,?_⟩,K.mono paid cap⟩
  intro y
  exact ⟨fun j=>j.elim,(hasSum_fintype _).summable,by simp⟩

/-- A forced singleton vanishes at the literal identity physical field. -/
theorem flat (K:sector) (t:T) : ((gallery K).density t 1).part (J.fire 0)=0 := by
  have none (j:ℕ) : K.hard t j 1=0 := by
    by_contra hn
    have forbidden := (K.charged t j 1 hn).1
    rw [Progress.DirectedRecipe.no_flags P.p.threshold_pos.le,inter_empty] at forbidden
    exact (P.activities.forced j).inventory_ne.ne_empty forbidden.symm
  have packetZero (s:Finset ℕ) : packet P.activities P.p (K.hard t) 1 s =
      if s=∅ then (1:Poly J) else 0 := by
    unfold packet
    by_cases h:s=∅
    · subst s
      simp [RG.Activities.admissible,Progress.DirectedRecipe.no_flags P.p.threshold_pos.le]
    · rw [if_neg h]
      split
      · obtain ⟨j,hj⟩:=nonempty_iff_ne_empty.mpr h
        exact Finset.prod_eq_zero hj (none j)
      · rfl
  have gas : (gallery K).gas t 1=1 := by
    change (∑' s,packet P.activities P.p (K.hard t) 1 s)=_
    simp_rw [packetZero]
    simp
  have noLamps : (gallery K).E.log t (1:Config G n)=0 := tsum_empty
  rw [Gallery.density,noLamps,Next.Rank.Exponential.pass_zero,gas,mul_one,Poly.part_smul]
  simp [Poly.one_part,J.fire_hot 0]

end YM.Integration.WilsonSingleHardRadius
