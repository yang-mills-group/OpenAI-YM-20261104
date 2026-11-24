import YM.Integration.WilsonCenteredNestedPairTicket
import YM.Integration.WilsonThermometerWeakPairRise

/-! Changing an input from its own homogeneous fiber to its actual
inclusion in the child horizon is exact in each restored physical row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRaised
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open WilsonCenteredNestedRealOrbit
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d e : I→ℕ}

lemma old (p : d≤e) (H:ℕ) (x:I→E4) (v:Labels S d) (o:E4) :
    shadowOld Q.port H x o (fun i=>F.sector.derivatives.rise (p i) (v i)) = shadowOld Q.port H x o v := by
  unfold shadowOld OPE.shadow
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun val : ℂ=>val • Q.port.loaded t H)
  symm
  apply WilsonThermometerWeakPairRise.coefficient Q.port Q.spans Q.continuum.laws.toSymmetric Q.lifts
  intro i
  refine Or.inr ⟨p i,?_⟩
  unfold names
  erw [S.rep,S.rep]

theorem spin (p : d≤e) (H:ℕ) (x:I→E4) (v:Labels S d) (o:E4) (k:Ortho) :
    spinning Q.port F.sector.turns H x o k (fun i=>F.sector.derivatives.rise (p i) (v i)) =
    spinning Q.port F.sector.turns H x o k v := by
  have commute : roll F.sector.turns k⁻¹ (fun i=> F.sector.derivatives.rise (p i) (v i)) =
      fun i=>F.sector.derivatives.rise (p i) ((roll F.sector.turns k⁻¹ v) i) :=
    funext (fun _=>Q.law.filtered ..)
  unfold spinning
  rw [commute]
  apply congrArg _
  exact old F Q p H _ _ _

theorem original (p : d≤e) (H:ℕ) (x:I→E4) (v:Labels S d) (o:E4) (k:Ortho) (b:Bool) :
    restored F Q.port H x (fun i=>F.sector.derivatives.rise (p i) (v i)) o k b =
    restored F Q.port H x v o k b := by
  cases b
  · exact spin F Q p H x v o k
  · have commute : bar F.room.kernel.spin (fun i=>F.sector.derivatives.rise (p i) (v i)) =
        fun i=>F.sector.derivatives.rise (p i) ((bar F.room.kernel.spin v) i) :=
      funext fun _=>Q.stands.realInc ..
    unfold restored
    simp only [if_true]
    rw [commute,spin F Q]

end YM.Integration.WilsonCenteredNestedRaised
