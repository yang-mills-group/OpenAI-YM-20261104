import YM.Integration.WilsonMixedFaceLog
import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! The actual disjoint re-inscription preserves every proper face on every auxiliary
period, before integration or taking the cofinal connected logarithm. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalJoinedCopyBank
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 AllOrder.Floe FVA1Physical.TwoReset WilsonMixedFaceLog
open WilsonMixedPassportRows WilsonMixedPassportArmada
open private centered from YM.Integration.WilsonMixedPassportRows
open scoped Classical BigOperators

section Faces
variable {G : Gauge} {n f : Side} {V α ι : Type} [DecidableEq V] {C : Census V}
  {P : Passport n V} (M : ι → Row P C G α) (how : n.val ∣ f.val)
  (w : V→ℕ) (q : ι → ℂ) {a : ℝ} {k : ℕ} (staff : Air.Staff M q w a k)
  (b : Fin (Pages n f)) (g : ℝ) (U : Config G f) (v : Multi.Hot C)
local notation "line" => (fun i:ι => FVA1Physical.TwoReset.copy how (M i) b)
local notation "modeAt" i:max => (ScatterR.actor line i).val
local notation "tariff" => (fun i:ι => if modeAt i = v.val then ScatterR.familyAt line q i g U else 0)

include staff in
private theorem face (inside : Finset V) :
    HasSum (fun i:Face M inside => tariff i.val)
      (if v.val.val ⊆ inside then Air.sums line q (fun i => modeAt i=v.val) g U else 0) := by
  have complete := (Air.usable_all line q w (copy_staff how M w q staff b) U g
    (fun i => modeAt i=v.val)).hasSum
  by_cases hs : v.val.val ⊆ inside
  · rw [if_pos hs]
    have support : Function.support tariff ⊆ {i | (M i).mode.val ⊆ inside} := by
      intro i alive
      have matchMode : modeAt i = v.val := by
        by_contra no
        exact alive (by simp only [if_neg no])
      change (modeAt i).val ⊆ inside
      rw [matchMode]
      exact hs
    apply (hasSum_subtype_iff_of_support_subset support).mpr
    apply complete.congr_fun
    intro j
    by_cases hit : modeAt j = v.val <;> simp_all
  · rw [if_neg hs]
    apply hasSum_zero.congr_fun
    intro i
    have excluded : modeAt i.val ≠ v.val := fun eq => hs (eq ▸ i.property)
    simp only [if_neg excluded]
end Faces

section Whole
variable {G : Gauge} {n f : Side} {V ι κ α β γ : Type} [DecidableEq V] {C : Census V}
  {P Q : Passport n V} (M : ι → Row P C G α) (Y : κ → Row Q C G β)
  (old fresh : Finset V) (apart : Disjoint old fresh) (l : γ → α) (r : γ → β)
  (w₀ w₁ w : V → ℕ) (layout : Layout G) (tape : Finset Age) (t : γ) (h : n.val ∣ f.val)
local notation "S" => routed M Y old fresh apart l r
local notation "p₀" => (fun i:ι=>(M i).paint (l t))
local notation "p₁" => (fun i:κ=>(Y i).paint (r t))
local notation "p₂" => (fun i=>(S i).paint t)
local notation "A" => copyColor h M w₀ p₀ layout tape
local notation "B" => copyColor h Y w₁ p₁ layout tape
local notation "J" => copyColor h S w p₂ layout tape
local notation "L₀" b:max => (fun i:ι=> FVA1Physical.TwoReset.copy h (M i) b)
local notation "L₁" b:max => (fun i:κ=> FVA1Physical.TwoReset.copy h (Y i) b)
local notation "L₂" b:max => (fun i=> FVA1Physical.TwoReset.copy h (S i) b)

/-- Join the independently named raw input colors with the actual joint marker grades. -/
def joined (o fresh : Finset V) (grades : V → ℕ) (left right : Bulk.Colors C G f) : Bulk.Colors C G f where
  vac := left.vac
  power v := Launch.index C grades v.val+1
  mark v := (if v.val.val⊆o then left.mark v else 0) + (if v.val.val⊆fresh then right.mark v else 0)

private theorem page (b : Fin (Pages n f)) (g : ℝ) (U : Config G f) (v : Multi.Hot C)
    {a₀ a₁ : ℝ} {k₀ k₁ : ℕ} (h₀ : Air.Staff M p₀ w₀ a₀ k₀) (h₁ : Air.Staff Y p₁ w₁ a₁ k₁) :
    (Air.craft (L₂ b) p₂ w layout tape).mark v g U =
      (if v.val.val ⊆ old then (Air.craft (L₀ b) p₀ w₀ layout tape).mark v g U else 0) +
      (if v.val.val ⊆ fresh then (Air.craft (L₁ b) p₁ w₁ layout tape).mark v g U else 0) := by
  let left (i:Face M old) := if (ScatterR.actor (L₀ b) i.val).val = v.val then
    ScatterR.familyAt (L₀ b) p₀ i.val g U else 0
  let right (i:Face Y fresh) := if (ScatterR.actor (L₁ b) i.val).val = v.val then
    ScatterR.familyAt (L₁ b) p₁ i.val g U else 0
  have z := HasSum.sum (f:=Sum.elim left right) (face M h w₀ p₀ h₀ b g U v old)
    (face Y h w₁ p₁ h₁ b g U v fresh)
  apply HasSum.tsum_eq
  apply z.congr_fun
  rintro (i|i)
  · let parent : ∀ v ∈ (M i.val).mode.val, owner P Q old v = P := fun _ hv => if_pos (i.property hv)
    have center0 := centered (owner P Q old) (M i.val) parent l
    have center : ((L₂ b) (Sum.inl i)).center = ((L₀ b) i.val).center := by
      rw [recenter, recenter]
      exact congrArg (fun y:Site n=>(FVA1Physical.TwoReset.page h y b).val) center0
    have term : ScatterR.familyAt (L₂ b) p₂ (Sum.inl i) g U = ScatterR.familyAt (L₀ b) p₀ i.val g U := by
      simp only [ScatterR.familyAt,center]
      rfl
    dsimp only [Sum.elim_inl]
    unfold left
    by_cases matchMode : (ScatterR.actor (L₀ b) i.val).val = v.val
    · simp only [if_pos matchMode, if_pos (show (ScatterR.actor (L₂ b) (.inl i)).val=v.val from matchMode), term]
    · simp only [if_neg matchMode, if_neg (show (ScatterR.actor (L₂ b) (.inl i)).val≠v.val from matchMode)]
  · let parent : ∀ v ∈ (Y i.val).mode.val, owner P Q old v = Q := fun _ hv =>
      if_neg (fun hv' => Finset.disjoint_left.mp apart hv' (i.property hv))
    have center0 := centered (owner P Q old) (Y i.val) parent r
    have center : ((L₂ b) (Sum.inr i)).center = ((L₁ b) i.val).center := by
      rw [recenter, recenter]
      exact congrArg (fun y:Site n=>(FVA1Physical.TwoReset.page h y b).val) center0
    have term : ScatterR.familyAt (L₂ b) p₂ (Sum.inr i) g U = ScatterR.familyAt (L₁ b) p₁ i.val g U := by
      simp only [ScatterR.familyAt,center]
      rfl
    dsimp only [Sum.elim_inr]
    unfold right
    by_cases matchMode : (ScatterR.actor (L₁ b) i.val).val = v.val
    · simp only [if_pos matchMode, if_pos (show (ScatterR.actor (L₂ b) (.inr i)).val=v.val from matchMode), term]
    · simp only [if_neg matchMode, if_neg (show (ScatterR.actor (L₂ b) (.inr i)).val≠v.val from matchMode)]

theorem original {a₀ a₁ : ℝ} {k₀ k₁ : ℕ} (h₀ : Air.Staff M p₀ w₀ a₀ k₀)
    (h₁ : Air.Staff Y p₁ w₁ a₁ k₁) : J = joined old fresh w A B := by
  have marks : (J).mark = (joined old fresh w A B).mark := by
    funext v g U
    simp only [copyColor, Finset.sum_apply, joined, Pi.add_apply]
    simp_rw [page M Y old fresh apart l r w₀ w₁ w layout tape t h _ g U v h₀ h₁]
    rw [Finset.sum_add_distrib]
    by_cases a : v.val.val ⊆ old <;> by_cases b : v.val.val ⊆ fresh <;>
      simp_all
  have eq_of {a b : Bulk.Colors C G f} (vac : a.vac=b.vac) (m : a.mark=b.mark)
      (power : a.power=b.power) : a=b := by
    cases a
    cases b
    cases vac
    cases m
    cases power
    rfl
  exact eq_of rfl marks rfl

end Whole
end YM.Integration.WilsonOriginalJoinedCopyBank
