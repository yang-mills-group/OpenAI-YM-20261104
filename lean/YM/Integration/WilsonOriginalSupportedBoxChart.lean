import YM.Integration.WilsonOriginalSmoothBoxSlice
import YM.Integration.WilsonOriginalInteriorValues

/-! A physical field supported strictly inside the cube gives its own periodic
reading. This applies to all genuine mixed derivatives of the localized field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSupportedBoxChart
open Set Filter Finset UnitAddTorus AddCircle
open WilsonOriginalCompactTorusChart (gate quotient)
open WilsonOriginalPhysicalBoxSlices (positions)
open scoped Topology BigOperators

abbrev Space (d : ℕ) := Fin d → ℝ
def Supported {d : ℕ} (l h : Space d) (f : Space d → ℂ) : Prop :=
  ∀ i x, x i ∉ Icc (l i) (h i) → f x = 0

def read {d : ℕ} (f : Space d → ℂ) (z : UnitAddTorus (Fin d)) : ℂ :=
  f (fun i => (equivIoc (1:ℝ) 0 (z i)).val)

theorem realValue {d : ℕ} {l h : Space d} {f : Space d → ℂ} (inside : Supported l h f)
    (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1) {x : Space d}
    (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) :
    read f (fun i => (x i : UnitAddCircle)) = f x := by
  by_cases proper : ∀ i, 0 < x i
  · have chart (i : Fin d) : (equivIoc (1:ℝ) 0 (x i)).val = x i :=
      equivIoc_coe_of_mem ⟨proper i,by simpa using (hx i).2⟩
    simp [read,chart]
  · obtain ⟨i,hi⟩ := not_forall.mp proper
    have eq : x i = 0 := le_antisymm (not_lt.mp hi) (hx i).1
    have endpoint : (equivIoc (1:ℝ) 0 (x i)).val = 1 := by
      have same : ((x i:ℝ):UnitAddCircle) = ((1:ℝ):UnitAddCircle) := by
        simpa only [eq,zero_add] using (AddCircle.coe_add_period (1:ℝ) (0:ℝ)).symm
      rw [same]
      exact equivIoc_coe_of_mem (by norm_num)
    rw [read,inside i x (by rw [eq]; exact fun e => (left i).not_ge e.1),inside i _]
    simpa only [endpoint] using (show (1:ℝ) ∉ Icc (l i) (h i) from fun e => (right i).not_ge e.2)

theorem continuous_read {d : ℕ} {l h : Space d} {f : Space d → ℂ} (inside : Supported l h f)
    (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1)
    (cont : ContinuousOn f {x | ∀ i, x i ∈ Icc (0:ℝ) 1}) : Continuous (read f) := by
  apply (quotient (0 : Space d)).continuous_iff.mpr
  let unbox (X : (i : Fin d) → Icc ((0 : Space d) i) ((0 : Space d) i+1)) := fun i => (X i).val
  have chart : Continuous unbox := by dsimp [unbox]; fun_prop
  apply (cont.comp_continuous chart (fun X i => by simpa [unbox] using (X i).property)).congr
  intro X
  exact (realValue inside left right (x:=unbox X) (fun i => by simpa [unbox] using (X i).property)).symm

theorem original {d : ℕ} {l h : Space (d+1)} {f : Space (d+1) → ℂ}
    (inside : Supported l h f) (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1)
    (i : Fin (d+1)) (rest : Fin d → UnitAddCircle) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (fun t : ℝ => read f (i.insertNth (t:UnitAddCircle) rest)) =ᶠ[𝓝 x]
      (fun t : ℝ => f (positions i 0 rest t)) := by
  have seats (z : UnitAddCircle) :
      (fun j => (equivIoc (1:ℝ) 0 ((i.insertNth z rest : Fin (d+1) → UnitAddCircle) j)).val) =
        positions i 0 rest (equivIoc (1:ℝ) 0 z).val := by
    funext j
    refine i.succAboveCases ?_ (fun k => ?_) j <;> simp [positions]
  simp only [read,seats]
  exact WilsonOriginalPeriodicWindowGerm.germ (fun t => f (positions i 0 rest t))
    (left i) (by simpa using right i) (fun t ht => inside i _ (by simpa [positions] using ht))
    (by simpa using hx)

end YM.Integration.WilsonOriginalSupportedBoxChart
