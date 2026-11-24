import YM.Integration.WilsonSurveyedColorNominated

/-! Replacing all promoted insertions in the same labelled MS tour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNamedTour
open Function Finset MS MS.Land MS.Local.Physical MS.Rake MS.Rake.Geo
open MS.Plane MS.High MS.LogTime MS.Latch
open FVA2 FVA2.Extras FVA2.O FVA2.O.Lives FVA2.O.Fuse FVA2.Position.OpenAxis
open WilsonSurveyedColorNominated WilsonSurveyedColorCurvature
open scoped Classical BigOperators
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
variable {W : Type} [LinearOrder W] (x : Position W Unit)
variable (label : W → Rake.Label (Press.portDeck G)) (s : Finset W)

def placed (L : List W) (u : W → Rake.Label (Press.portDeck G)) (i : W) :=
  if i ∈ L then letIn (label i).h (logMass a) (field hG U same M a (label i)).inserted
  else rowM (Tide.frameF Unit a) M (u i)

def toured : List W → (W → Rake.Label (Press.portDeck G)) → ℕ → ℂ
  | [], u, n => Dial.tour M u a (fun i => x i ()) s n
  | i :: L, u, n =>
    ∑ k : Plaid (Press.portDeck G) (label i).h, ∑ j ∈ range (n+1),
      ((field hG U same M a (label i)).coefficients j k : ℂ) *
        toured L (update u i ⟨(label i).h,k⟩) (n-j)

theorem measured (hx : Mesh (Tide.frameF Unit a) x) (L : List W)
    (once : L.Nodup) (present : ∀ i ∈ L, i ∈ s) (u : W → Rake.Label (Press.portDeck G)) (n : ℕ) :
    service a M (placed hG U same M a label L u) x s n =
      toured hG U same M a x label s L u n := by
  have seated (l : List W) (v : W → Rake.Label (Press.portDeck G)) :
      Survey (Tide.frameF Unit a) M (placed hG U same M a label l v) x := by
    intro i
    by_cases hi : i ∈ l
    · simpa only [placed,if_pos hi] using (field hG U same M a (label i)).reduced.usable (x i)
    · simp only [placed,if_neg hi]
      exact Estate (cometClean (M.markOK _ (v i).item)) (Response.visit _) _
  have certified (l : List W) (v : W → Rake.Label (Press.portDeck G)) (i : W) :
      Certified (placed hG U same M a label l v i) M (logMass a) 0 := by
    by_cases hi : i ∈ l
    · simpa only [placed,if_pos hi] using (field hG U same M a (label i)).reduced.equipped.1
    · simp only [placed,if_neg hi]
      exact Certified.first (v i).item
  induction L generalizing u n with
  | nil =>
    apply tourC (seated [] u) hx u
    funext i
    simp [placed]
  | cons i l ih =>
    have hi := List.nodup_cons.mp once
    rw [toured, (field hG U same M a (label i)).reduced.involves W inferInstance x _ i
      (by simp [placed]) (seated (i :: l) u) hx s (present i (by simp))
      (fun j _ => certified (i :: l) u j) n]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro j _
    congr 1
    have hem : swapField a M i k (placed hG U same M a label (i :: l) u) =
        placed hG U same M a label l (update u i ⟨(label i).h,k⟩) := by
      funext w
      by_cases he : w = i
      · subst w
        simp [swapField, placed, hi.1]
        rfl
      · simp [swapField, placed, he]
    rw [hem]
    exact ih hi.2 (fun j hj => present j (List.mem_cons_of_mem i hj)) _ _

end YM.Integration.WilsonSurveyedColorNamedTour
end
