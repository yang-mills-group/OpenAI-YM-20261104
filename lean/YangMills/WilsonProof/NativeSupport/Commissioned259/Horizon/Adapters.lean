import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Ordinary
/-! # From words on the actual tree leaves to the physical slot organization (G.4)

Names adapted to the requested inputs. No price re-expression through single-coordinate
windows smaller in period, no reduction of the physical exterior marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Finset Filter Set MeasureTheory Table Extraction Spec Arboreal Orbits Node Log
open scoped Topology Classical BigOperators
variable {G:Gauge}{L:Register G} {S:Table L} {Q:DiffPlan S} {C:Family G}
    {I J : Type} [Fintype I] [Fintype J]
private lemma named_layout {X J:Type} [Fintype X] [Fintype J] (H:Finset X) (T:Table L) (hT:T.Symmetric)
    (x:X→ E4)(u:X→L.Token) (e:J≃H) (y:J→E4)(v:J→L.Token)
    (hp:∀ j, y j=x (e j).val) (hi:∀ j, v j=u (e j).val) (hk:Injective y) :
    Arboreal.whole T H x u (Chart.bare:Fin 0→E4) Chart.bare=observe T y v := by
  let E:=Equiv.sumEmpty (↥H) (Fin 0)
  let r:=E.trans e.symm
  have p: beside (crop x H) (Chart.bare:Fin 0→E4) = y ∘ r := funext fun q=> by
    cases q with
    | inl i => obtain ⟨i,rfl⟩:= e.surjective i; simpa [crop,r,E] using (hp i).symm
    | inr i => exact Fin.elim0 i
  have v: beside (crop u H) (Chart.bare:Fin 0→L.Token)= v ∘ r := funext fun q=> by
    cases q with
    | inl i=> obtain ⟨i,rfl⟩:= e.surjective i; simpa [crop,r,E] using (hi i).symm
    | inr i=> exact Fin.elim0 i
  rw [Arboreal.whole,p,v]; exact perm_observe T hT r _ hk

private def visitF (i:I⊕J): ↥((frame I J).leaves) := match i with
 | .inl i => ⟨leaf i, by rw [leaves]; simp⟩
 | .inr j=> ⟨far j, by rw [leaves]; simp⟩
def leafSlot : (I⊕J) ≃ ((frame I J).leaves) := Equiv.ofBijective visitF (by
  constructor
  · rintro (i|i) (j|j) h <;> (have h:=congr_arg Subtype.val h; dsimp only [visitF] at h; cases h <;> rfl)
  intro u; obtain ⟨a,h⟩:=u; cases a with
  | base | child => simp [leaves,near,rim] at h
  | far i => exact ⟨.inr i,rfl⟩
  | leaf i=> exact ⟨.inl i,rfl⟩)
private def visitO (i:Unit⊕J): ↥(outer I J) := match i with
  | .inl _=>⟨child,by simp [outer]⟩
  | .inr i=>⟨far i,by simp [outer]⟩
def farSlot : (Unit ⊕ J) ≃ outer I J := Equiv.ofBijective visitO (by
  constructor
  · rintro (⟨⟩|i) (⟨⟩|j) h <;> (have h:=congr_arg Subtype.val h; dsimp only [visitO] at h; cases h <;> rfl)
  intro u; obtain ⟨a,h⟩:=u; cases a with
  | base | leaf i => simp [outer,rim] at h
  | child => exact ⟨.inl (),rfl⟩
  | far i=> exact ⟨.inr i,rfl⟩)

/-- All other tokens are unit place (arbitrary; not exposed). -/
def cards (u:I→L.Token)(v:J→L.Token): Node I J→L.Token
  | base|child => L.one 0
  | leaf i => u i
  | far j=> v j
lemma as_full (T:Table L) (h:T.Symmetric) (o:E4) (r t : ℝ) (x:I→E4)(y:J→E4)(u:I→L.Token)(v:J→L.Token)
    (hi:Injective (beside (atPosition o r x) (atPosition o t y))) :
    Arboreal.whole T (frame I J).leaves (sites o r t x y) (cards u v) (Chart.bare:Fin 0→E4) Chart.bare =
        observe T (beside (atPosition o r x) (atPosition o t y)) (beside u v) :=
  named_layout _ T h _ _ leafSlot _ _ (fun | .inl i =>rfl| .inr i=>rfl) (fun | .inl i=>rfl | .inr i=>rfl) hi
lemma as_term (T:Table L) (P:Prescription Q) (h:T.Symmetric) (hS:S.Symmetric) (o:E4) (r t:ℝ) (x:I→E4)(y:J→E4)(u:I→L.Token)(v:J→L.Token)
    (a:Mode Q) (hi:Injective (beside (sole o) (atPosition o t y))) :
    let w:=cards u v; let z:=sites o r t x y
    coalesce P (near I J) z w child a * Arboreal.whole T (outer I J) z (update w child (P.letter a)) (Chart.bare:Fin 0→E4) Chart.bare =
      P.termRead T (atPosition o r x) u o a (atPosition o t y) v := by
  intro w z
  have hh : P.ope a (crop z (near I J)) (crop w (near I J)) o = P.ope a (atPosition o r x) u o :=
     (P.coefficient_perm _ hS nearSeat a).symm
  apply congr_arg₂ (· * ·) hh
  refine named_layout _ T h _ _ farSlot _ _ ?_ ?_ hi
  · intro i; cases i <;> rfl
  rintro (i|j)
  · change P.letter a= Function.update w child (P.letter a) child; simp
  change w (far j) = Function.update w child (P.letter a) (far j); exact (update_of_ne (by simp : far j ≠ (child:Node I J)) ..).symm
end YM.OPE.Flash259HorizonFork
