import YM.Cells.Embedded
import YM.Cells.Interior

/-! One reflected price for a signed joint change at the independently occupied chambers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReflectedProducts
open Function Filter Set MeasureTheory Finset Lattice Wilson Cells
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (T : Tiling n) (c : ι → T.Cell) (P D : ι → Config G n → ℂ)

def branch (s : Finset ι) (i : ι) := if i∈s then D i else P i

def word (s : Finset ι) (U : Config G n) := ∏ i, T.copy (c i) (branch P D s i) U

theorem split (U : Config G n) : (∏ i, (T.copy (c i) (P i) U+T.copy (c i) (D i) U))
    = ∑ s : Finset ι, word T c P D s U := by
  classical
  rw [show (∏ i, (T.copy (c i) (P i) U+T.copy (c i) (D i) U)) =
       ∏ i, (T.copy (c i) (D i) U+T.copy (c i) (P i) U) by simp only [add_comm]]
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro s _
  unfold word
  have choice (i : ι) : T.copy (c i) (branch P D s i) U =
      if i∈s then T.copy (c i) (D i) U else T.copy (c i) (P i) U := by
    by_cases hi:i∈s <;> simp [branch,hi]
  simp_rw [choice]
  rw [Finset.prod_ite]
  simp [Finset.sdiff_eq_filter]

theorem priced (β : ℝ) (seam : Seam G n β) (distinct : Injective c)
    (hP : ∀ i, Interior (T.chamber 0) (P i)) (hD : ∀ i, Interior (T.chamber 0) (D i)) :
    ‖moment β (fun U=>∏ i, (T.copy (c i) (P i) U+T.copy (c i) (D i) U)) -
      moment β (fun U=>∏ i, T.copy (c i) (P i) U)‖ ≤
        ∑ s ∈ (Finset.univ : Finset (Finset ι)).erase ∅, ∏ i, T.rootTest β (branch P D s i) := by
  classical
  have localRow (s : Finset ι) (i : ι) : Interior (T.chamber 0) (branch P D s i) := by
    by_cases j:i∈s <;> simp only [branch,j,if_true,if_false] <;> first | exact hP i | exact hD i
  have finite (s : Finset ι) : Integrable (word T c P D s) (law G n β) :=
    (Interior.combines (K:=Set.univ) (fun i=>T.copy (c i) (branch P D s i)) univ
      fun i _ => (T.copies (c i) (localRow s i)).enlarges (subset_univ _)).integrable β
  have table : moment β (fun U=>∏ i, (T.copy (c i) (P i) U+T.copy (c i) (D i) U)) =
      ∑ s : Finset ι, moment β (word T c P D s) := by
    simp only [moment,split]
    exact integral_finsetSum _ (fun s _=>finite s)
  have blank : word T c P D ∅ = (fun U=>∏ i, T.copy (c i) (P i) U) := by
    funext U
    simp [word,branch]
  have cut := Finset.sum_erase_add (s:=(univ : Finset (Finset ι))) (fun s=>moment β (word T c P D s))
    (Finset.mem_univ (∅ : Finset ι))
  rw [table,←blank,←cut,add_sub_cancel_right]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun s _=>T.planted seam c distinct _ (localRow s))

end YM.Integration.WilsonThermometerReflectedProducts
