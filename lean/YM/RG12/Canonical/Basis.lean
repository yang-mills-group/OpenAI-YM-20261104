import YM.RG12.Canonical.FromFrames

/-!
# Examples of compatible bases on the *same* construction
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Desk
open Function Filter Finset Lattice RG Source Frames Table OPE
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} (B : DiffPlan S)

/-- Physical blocks. Can equally use any other compatible splitting; export adapters to `Q`
& `P` in the consumers to track induced grading. -/
abbrev Sector (d : ℕ) (i : Grade d) := Qname B i → ℂ

variable {B}
def enter (Q : Prescription B) (d : ℕ) : Col (Sector B d) →ₗ[ℂ] S.Field d :=
    ∑ i : Grade d, ∑ j: Qname B i, (((LinearMap.proj j).comp
      (LinearMap.proj i : Col (Sector B d) →ₗ[ℂ] (Sector B d i))).smulRight
        (Q.loaded ⟨i,j⟩ d))

lemma paid (Q:Prescription B) (d:ℕ) (x : Col (Sector B d)) :
    enter Q d x=∑ i:Grade d,∑ j:Qname B i,x i j • Q.loaded ⟨i,j⟩ d:=by
  unfold enter; simp

def exit (Q:Prescription B) (d : ℕ) (x : S.Field d) : Col (Sector B d) :=
    fun i j=> Q.test ⟨i,j⟩ d x

lemma accept (Q:Prescription B) (d:ℕ) (hq:Q.Coherent) (x : S.Field d) :
    enter Q d (exit Q d x) = x := by
  refine (paid ..).trans (Eq.trans ?_ ((hq d).rebuilds x))
  unfold OPE.bands; rw [sum_sigma,sum_range]; rfl

lemma returns (Q : Prescription B) (d:ℕ) (hq:Q.Coherent) (x : Col (Sector B d)) :
    exit Q d (enter Q d x) = x := by
  have he (i j) : Sigma.mk (β:=fun i=>Fin (addition B i)) (i:Grade d).val j∈ bands B d:= (full_bands ..).mpr i.is_le
  funext i j
  change Q.test _ _ _= x i j; rw [paid,map_sum]
  simp_rw [map_sum, map_smul, (hq d).bothWays ⟨i,j⟩ ⟨_,_⟩ (he i j) (he _ _)]
  rw [sum_eq_single i]
  · rw [sum_eq_single j]; rw [if_pos rfl]; exact mul_one _
    · intro b hb hi; rw [if_neg (by simpa using hi.symm),smul_zero]
    simp
  · intro b hb hi; apply sum_eq_zero; intro c hc
    rw [if_neg ?_,smul_zero]; intro h; have hx:= congr_arg Sigma.fst h; exact hi ((Fin.ext hx).symm)
  simp

def official (Q:Prescription B) (hq:Q.Coherent) (d:ℕ) : Col (Sector B d) ≃ₗ[ℂ] S.Field d :=
  LinearEquiv.ofBijective (enter Q d)
    ⟨Function.LeftInverse.injective (returns Q d hq), Function.RightInverse.surjective (accept Q d hq)⟩

lemma own (Q:Prescription B) (hq:Q.Coherent) (d:ℕ) (i:Grade d) (x:Sector B d i):
    official Q hq d (Frames.put _ i x)= ∑ j, x j • Q.loaded ⟨i,j⟩ d := by
  change enter _ _ _= _; rw [paid,sum_eq_single i, Frames.put,Pi.single_eq_same]
  · intro b hb hi; rw [Frames.put,Pi.single_eq_of_ne hi]; simp
  simp

lemma fits (Q:Prescription B) (hq:Q.Coherent) (d:ℕ) (i:Grade d) (x:Sector B d i):
    official Q hq d (Frames.put _ i x) ∈ LinearMap.range (B.rise i.is_le) := by
  rw [own]
  exact Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (by
    rw [Q.cost _ ((full_bands ..).mpr i.is_le)]; exact LinearMap.mem_range_self _ _)

lemma rises (Q:Prescription B) (hq:Q.Coherent) (d:ℕ) (hS:S.Symmetric) (hB:B.Inclusions S)
    (i:Grade d) (x:S.Field i.val) : (official Q hq d).symm (B.rise i.is_le x)∈ Frames.flag (Sector B d) i:=by
  have he(v) : (official Q hq d).symm v=exit Q d v:= ((official Q hq d).injective (by
    rw [LinearEquiv.apply_symm_apply]; exact (accept Q d hq v).symm))
  rw [he]; intro j hj; ext k
  change Q.test ⟨j,k⟩ d (B.rise i.is_le x)=0
  rw [← (hq i).rebuilds x,map_sum,map_sum]; refine sum_eq_zero fun t ht=> ?_
  have hh:= (full_bands ..).mp ht
  rw [map_smul,map_smul,← Prescription.load_next ..]
  rw [(hq d).bothWays ⟨j,k⟩ t ((full_bands ..).mpr j.is_le) ((full_bands ..).mpr (hh.trans i.is_le)), if_neg (show (⟨j,k⟩: Mode B) ≠ t from fun h=> not_le_of_gt (show i.val<j.val from hj) ((congr_arg Sigma.fst h).trans_le hh)),smul_zero] -- h ▸ doesn't substitute pair into hh?
  all_goals assumption

/-- Calibrating moving frames at each own horizon (without reference to official
basis, which only explains the grading) gives the fixed compatibility.
 Heights P of `Consecutive` can therefore use these exact reference frames;
 producers need only verify test-unit compatibility for columns in the finite
 physical quotient, e.g. calibrate own-horizon with physical pivots.
 No compatibility of independently renormalized offshell letters assumed here.
-/
lemma compatible (Q:Prescription B) (hq:Q.Coherent) (d:ℕ) (hS:S.Symmetric) (hB:B.Inclusions S)
    (Y: Col (Sector B d) →ₗ[ℂ] S.Field d) (hY:∀ (i:Grade d) (x:Sector B d i), Y (Frames.put _ i x)∈ LinearMap.range (B.rise i.is_le)):
    Frames.triangular _ ((official Q hq d).symm.toLinearMap.comp Y):=by
  intro i j h x
  obtain ⟨v,hv⟩:=hY _ x
  change (official Q hq d).symm _ i = 0; rw [← hv]; exact rises Q hq d hS hB _ v i h

end YM.RG12.Desk
