import YM.Integration.WilsonCenteredCapturedHardFace
import YM.Push.LOCAL_SPLITTING.Products

/-! Bill each genuine rendered regular product at its common center.
The extra halo is enforced by an exact signed hard rebate, retaining the
original branch masks wherever an original value is actually used. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureRegularAtoms
open Function Finset Lattice RG Wilson Marker QuadraticLocal Ac Push.Local Push.Corrected
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι J : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {p : BudgetPoint}
    (L : Lamps X ι G p o R) (s : Finset J) (site : J→ι) (x : X)

def domain (Z : Support n) := Z ∪ s.biUnion (fun i=>L.ground (site i))
def viewed : Config G n→ℂ := fun U=>∏ i∈s,L.light x (site i) U
def nominal : Config G n→ℂ := ∏ i∈s,L.nominal x (site i)
def rebate (Z : Support n) := viewed L s site x - masked p.threshold (domain L s site Z) (nominal L s site x)

theorem attends (Z : Support n) {i : J} (hi : i∈s) : L.ground (site i) ⊆ domain L s site Z :=
  fun _ hy=>mem_union_right _ (mem_biUnion.mpr ⟨i,hi,hy⟩)

theorem even (Z : Support n) (U : Config G n) (good : Healthy p.threshold (domain L s site Z) U) :
    viewed L s site x U = nominal L s site x U := by
  change (∏ i∈s,L.light x (site i) U) = (∏ i∈s,L.nominal x (site i)) U
  rw [Finset.prod_apply]
  apply prod_congr rfl
  intro i hi
  unfold Lamps.light
  split
  · rfl
  exact masked_eq _ _ _ _ (good.mono_left (attends L s site Z hi))

theorem posted (Z : Support n) :
    viewed L s site x = masked p.threshold (domain L s site Z) (nominal L s site x) + rebate L s site x Z := by
  unfold rebate
  abel

theorem original (Z : Support n) (y : Site n) (b : J → Site n) (rad : ℕ)
    (near : ∀ i ∈ s, separation (b i) y ≤ rad)
    (e : ι→ℝ) (price : ∀ i∈s,p.supBounds (b i) (L.ground (site i)) (L.nominal x (site i)) (e (site i))) :
    let T := domain L s site Z
    let f := nominal L s site x
    let h := rebate L s site x Z
    let stage := (((s.card+1:ℕ) : ℝ)*(1+(rad:ℝ))^p.power)^p.order
    p.Regular T f ∧ p.supBounds y T f (stage*∏ i∈s,e (site i)) ∧
      Attaches p.threshold T h ∧ (∀ U, ‖h U‖ ≤ ∏ i∈s,e (site i)) := by
  intro T f h stage
  obtain ⟨good,bound⟩ := price_product (B:=p) (Y:=T) s (fun i=>L.nominal x (site i)) (fun i=>e (site i)) y b rad near
    (fun i=>L.ground (site i)) (fun _ hi=>attends L s site Z hi) (fun i _=>L.legal x (site i)) price
  have reg i (hi : i∈s) : Width.LocalCharge p o T (fun U=>L.frame (site i) x U) :=
    (QuadraticLocal.Shelter.Deck.locality (L:=L) x (site i)).widen (attends L s site Z hi)
  have full (i : J) (U : Config G n) : (L.frame (site i) x U).part (L.mode (site i)) = L.light x (site i) U := by
    simp [Lamps.frame,Poly.part_send]
  have meas : Measurable (viewed L s site x) := by
    change Measurable fun U=>∏ i∈s,L.light x (site i) U
    apply Finset.measurable_fun_prod
    intro i hi
    rw [←funext (full i)]
    exact (Poly.part_cont _).measurable.comp (reg i hi).borel
  have locals : UsesFinal p.threshold T (viewed L s site x) := by
    intro U V same fields
    apply prod_congr rfl
    intro i hi
    rw [←full i U,←full i V]
    exact congrArg (fun A : Poly R=>A.part (L.mode (site i))) ((reg i hi).reads U V same fields)
  have symmetry : GaugeInvariant (viewed L s site x) := by
    intro g U
    apply prod_congr rfl
    intro i hi
    rw [←full i _,←full i U]
    exact congrArg (fun A : Poly R=>A.part (L.mode (site i))) ((reg i hi).gauge g U)
  refine ⟨good,bound,⟨?_,?_,meas.sub (masked_measurable _ _ _ good.borel),?_⟩,?_⟩
  · intro U V reads flags
    exact congrArg₂ (·-·) (locals U V reads flags) (uses_mask _ good.sites U V reads flags)
  · intro g U
    exact congrArg₂ (·-·) (symmetry g U) (invariant_mask good.symmetry _ _ g U)
  · intro U healthy
    exact sub_eq_zero.mpr ((even L s site x Z U healthy).trans (masked_eq _ _ _ _ healthy).symm)
  intro U
  by_cases yes : Healthy p.threshold T U
  · have eq : h U = 0 := sub_eq_zero.mpr ((even L s site x Z U yes).trans (masked_eq _ _ _ _ yes).symm)
    rw [eq,norm_zero]
    exact prod_nonneg fun i hi=>(price i hi).1
  · change ‖viewed L s site x U-masked p.threshold T f U‖ ≤ _
    rw [masked_ne _ _ _ _ yes,sub_zero]
    change ‖∏ i∈s,L.light x (site i) U‖ ≤ _
    rw [norm_prod]
    apply prod_le_prod (fun _ _=>norm_nonneg _)
    intro i hi
    by_cases clr : L.clear (site i)
    · rw [Lamps.light,if_pos clr,L.pure x (site i) U clr]
      exact (price i hi).2 1 (Next.Foundations.one_healthy _ _ p.threshold_pos.le) [] (Nat.zero_le _) (by simp)
    unfold Lamps.light
    rw [if_neg clr]
    by_cases pass : Healthy p.threshold (L.ground (site i)) U
    · rw [masked_eq _ _ _ _ pass]
      exact (price i hi).2 U pass [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ pass,norm_zero]
    exact (price i hi).1

end YM.Integration.WilsonCenteredCaptureRegularAtoms
