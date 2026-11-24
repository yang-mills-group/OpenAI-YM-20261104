import YM.Integration.WilsonSurveyedColorVacuumSolve

/-! The bulk and marked equations of the nominated dimensional MS book at
every perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumBook
open Function Set Filter MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path Oceans
open Landau Alps Garment Shine Hem Mell Pearl Train Dock Land Motif Literal Emit
open FVA2 FVA2.Position.OpenAxis FVA2.Extras
open WilsonSurveyedColorCurvature WilsonSurveyedColorSubtraction
open WilsonSurveyedColorNominated WilsonSurveyedColorVacuumDrive WilsonSurveyedColorVacuumSolve
open scoped Classical BigOperators Topology
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G)))

omit [PreconnectedSpace G.El] in
include same in
theorem vacuum (k : ℕ) : Pact (ledger U (M.bulk k)) (M.bulk k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨⟨_,hk⟩,_⟩ := M.bulkOK k
    apply one U hk hk
    · rw [bulk]
      exact pb_u k _ _ ih
    · exact Eventually.of_forall fun z => congrFun (initial U same k) z

omit [PreconnectedSpace G.El] in
private theorem boomCoeff (P : Box (Mob G)) (k : ℕ) :
    (Boom 0 (allDims U) P) k = allDims U (P k) := by
  induction P using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  | single i F =>
    rw [Boom_sl,zero_add]
    by_cases e : i=k
    · subst k; simp
    · simp only [Finsupp.single_eq_of_ne (Ne.symm e),map_zero]

theorem inlet (i : Rake.Label (Press.portDeck G)) (k : ℕ) :
    coat U (gloss (Literal.linear (Mob G) ((Plot (Press.portDeck G)).optics i.h i.item)) k) =
      gloss (Literal.linear (Mob G) (additional hG U same i)) k := by
  let P := (Plot (Press.portDeck G)).optics i.h i.item
  let Q := additional hG U same i
  let D := Boom 0 (allDims U) P - Q
  have evaluated (x : ℂ) : Literal.value (Mob G) x D = 0 := by
    dsimp only [D]
    rw [map_sub,linear_v,sub_eq_zero]
    funext m
    exact actual hG U same i x m
  funext z m w
  let K : Mob G →ₗ[ℂ] ℂ := {
    toFun F := F m w, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have pay := valuedZ D K (fun x => by rw [evaluated,map_zero]) k
  rw [hiss] at pay
  change ((Boom 0 (allDims U) P) k m w - Q k m w) = 0 at pay
  rw [boomCoeff] at pay
  exact sub_eq_zero.mp pay

theorem inserted (a : ℝ) (i : Rake.Label (Press.portDeck G)) (k : ℕ) :
    Pact (ledger U (M.marks i.h i.item k)) ((field hG U same M a i).inserted k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨⟨_,left⟩,_⟩ := M.markOK i.h i.item k
    obtain ⟨⟨_,right⟩,_⟩ := (field hG U same M a i).reduced.okay k
    apply one U left right
    · rw [marked]
      exact pm_u (vacuum U same M) k _ _ ih
    · exact Eventually.of_forall fun z => congrFun (inlet hG U same i k) z

end YM.Integration.WilsonSurveyedColorVacuumBook
end
