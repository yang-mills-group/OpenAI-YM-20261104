import YM.Integration.WilsonCenteredNestedPairChord

/-! The original held orbit and real choice define one complex multilinear
map in all of the deposited fields, before their common Haar integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedJointLinear
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open WilsonCenteredNestedRealOrbit WilsonCenteredNestedShadowBasis
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

include Q in
lemma old (P : Prescription F.sector.derivatives) (H : ℕ) (x : I→E4) (o:E4) (v:Labels S d) :
    older F P H x o v=shadowOld P H x o v := by
  unfold older shadowOld shadow
  simp only [_root_.sum_apply,LinearMap.compMultilinearMap_apply,check_eq P _ Q.continuum,LinearMap.toSpanSingleton_apply]

def turn (P : Prescription F.sector.derivatives) (H : ℕ) (x : I→E4) (o:E4) (k:Ortho) :
    MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field H) :=
  (F.sector.turns.act H k).toLinearMap.compMultilinearMap
    ((older F P H (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o)).compLinearMap
      (fun i=>(F.sector.turns.act (d i) k⁻¹).toLinearMap))

private def star (H:ℕ) (A:MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field H)) :
    MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field H) := by
  classical
  let ρ := F.room.kernel.spin
  refine ⟨fun v=>S.conj ρ H (A (bar ρ v)),?_,?_⟩
  all_goals
    intro dec
    cases Subsingleton.elim dec (Classical.decEq _)
    have updated (v:Labels S d)(i:I)(a:S.Field (d i)) :
        bar ρ (update v i a)=update (bar ρ v) i (S.conj ρ _ a) := by
      funext j
      by_cases he:j=i
      · subst j;rw [update_self];exact congr_arg _ (update_self i a v)
      · rw [update_of_ne he]
        exact congrArg (fun z=>S.conj ρ _ z) (@update_of_ne I (S.Field ∘ d) _ j i he a v)
  · intro v z a b;rw [updated,updated,updated,map_add,A.map_update_add,map_add]
  · intro v i a b;rw [updated,updated,map_smulₛₗ,A.map_update_smul,map_smulₛₗ];simp

def field (P : Prescription F.sector.derivatives) (H : ℕ) (x : I→E4) (o:E4) (k:Ortho) (b:Bool) :
    MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field H) :=
  if b then star F H (turn F P H x o k) else turn F P H x o k

include Q in
lemma original (P : Prescription F.sector.derivatives) (H : ℕ) (x : I→E4) (o:E4) (k:Ortho) (b:Bool) (v:Labels S d) :
    field F P H x o k b v=restored F P H x v o k b := by
  have arrow (w:Labels S d) : turn F P H x o k w=spinning P F.sector.turns H x o k w := by
    change F.sector.turns.act H k (older F P H _ _ (roll F.sector.turns k⁻¹ w))=_
    rw [old F Q]
    rfl
  cases b
  · exact arrow v
  · change S.conj F.room.kernel.spin H (turn F P H x o k (bar F.room.kernel.spin v))=S.conj F.room.kernel.spin H (spinning P F.sector.turns H x o k (bar F.room.kernel.spin v))
    rw [arrow]

end YM.Integration.WilsonCenteredNestedJointLinear
