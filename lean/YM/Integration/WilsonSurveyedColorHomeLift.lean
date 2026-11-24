import YM.Integration.WilsonSurveyedColorNominatedOPE

/-! Color naturality of the actual real Maxwell projection defining the
nonnegative-weight MS port deck. The auxiliary complement lives in the
spacetime tensor factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorHomeLift
open Function Labels Maxwell Maxwell.Free XSpace XSpace.On MS.Theater FVA2
open WilsonSurveyedColorPlot WilsonSurveyedColorOpenIndex
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {j h n : ℕ}
local notation "L" => U.toContinuousLinearEquiv.toContinuousLinearMap

theorem curl (A : Taylor G j) :
    takeCurl (color U j A) = rawMap j L (takeCurl A) := by
  funext a b
  ext1 v
  change _ = U (takeCurl A a b v)
  unfold takeCurl color
  simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_apply, sub_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  rw [map_smul,map_sub]
  rfl

theorem shell (A : Shell G j) : gaugeJet (faceMap j L A) = color U j (gaugeJet A) := by
  apply potential.injective
  apply Subtype.ext
  change takeCurl _ = takeCurl _
  rw [match_leg,curl,match_leg]
  rfl

theorem assignColor (A : Taylor G j) :
    assign G j (color U j A) = faceMap j L (assign G j A) := by
  change demark G j (takeCurl _) = _
  rw [curl]
  exact demark_cast .. 

theorem rotate (s : Ortho) (A : Taylor G j) :
    color U j (Taylor.turn s A) = Taylor.turn s (color U j A) := by
  apply Taylor.value_ext
  funext k x
  have leg (X : Taylor G j) (l : Axis) (z : E4) :
      (color U j X).value l z = U (X.value l z) := rfl
  simp only [leg,Taylor.turn_value,map_sum,map_smul]

theorem projected (A : Taylor G j) :
    On.solve G j (color U j A) = faceMap j L (On.solve G j A) := by
  have ht (t : Ortho) (x : Shell G j) :
      solutionTurn t (faceMap j L x) = faceMap j L (solutionTurn t x) := by
    apply LeftInverse.injective (f := gaugeJet (G := G) (j := j)) (g := On.solve G j) On.on_shell
    rw [← gauge_orient,shell,shell,← gauge_orient,rotate]
  unfold On.solve
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,On.legmap,
    LinearMap.comp_apply,← rotate,assignColor,ht]

theorem atRank (A : Taylor G j) :
    color U j (gaugeJet (On.solve G j A)) = gaugeJet (On.solve G j (color U j A)) := by
  rw [projected U (j := j) A,shell U (On.solve G j A)]

theorem jetted (A : Labels.Jet G) :
    changedJet (color U) (fun i => gaugeJet (On.solve G i (A i))) =
      (fun i => gaugeJet (On.solve G i (changedJet (color U) A i))) := by
  unfold changedJet
  funext i
  dsimp only
  rw [atRank (G := G) U (j := i) (A i)]

theorem liftedChange (p : Labels.Pol G) :
    On.lifting (reduceEq (changed (color U) p)) = changed (color U) (On.lifting (reduceEq p)) := by
  apply Labels.eval_ext
  intro A
  rw [On.lifted,jet_value,eval_changed,eval_changed,On.lifted,jet_value,jetted]

theorem preserves (N : Normalizes U) (p : Film0 G h n) :
    Press.refineF G h n (promoted U N p) = promoted U N (Press.refineF G h n p) :=
  Subtype.ext (liftedChange U p.val)

end YM.Integration.WilsonSurveyedColorHomeLift
end
