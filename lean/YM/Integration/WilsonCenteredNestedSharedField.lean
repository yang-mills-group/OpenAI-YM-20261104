import YM.Integration.WilsonCenteredNestedRawDiagram
import YM.Integration.WilsonCenteredNestedTerminalOrbit

/-! Read both complete raw fields through one and the same orthogonal
and real branch. The child transformation cancels at its true parent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedSharedField
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedDepositedField WilsonCenteredNestedTicketSites
open WilsonCenteredNestedRealOrbit WilsonCenteredNestedTerminalOrbit WilsonCenteredNestedRawDiagram
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRawPair WilsonCenteredNestedPairTicket
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def entrants (v:Fin 3→S.Tag) (k:Ortho) (b:Bool) : Fin 3→S.Tag :=
  fun j=>⟨(v j).1,into F (v j).1 k b (v j).2⟩

lemma cropPair {U V:Type} (j l:Fin 5) (h:U→V) (x:Fin 5→U) : pair (h ∘x) j l = h ∘ pair x j l := by
  funext i;fin_cases i <;> rfl

lemma cropTrio {U V:Type} (h:U→V) (x:Fin 5→U) : trio (h∘x) = h ∘ trio x := by
  funext i;fin_cases i <;> rfl

lemma child_return (D:ℕ) (X:Fin 5→E4) (v:Fin 3→S.Tag) (k:Ortho) (b:Bool) :
    restored F Q.port D (pair X 2 3) (voices (head v)) (X 1) k b =
      out F D k b (child F Q D (Ortho.move k⁻¹ ∘X) (entrants F v k b)) := by
  rw [currency,child,cropPair]
  apply congrArg (out F D k b)
  unfold shadowOld
  apply congrArg (fun w=>OPE.shadow Q.port D (Ortho.move k⁻¹ ∘pair X 2 3) w (Ortho.move k⁻¹ (X 1)))
  funext i;fin_cases i <;> rfl

theorem joined_return (D H m:ℕ) (c:Q.channels m) (X:Fin 5→E4) (v:Fin 3→S.Tag) (k:Ortho) (b:Bool) :
    joined F Q Q.port D H m c (head v) (v 2) (pair X 2 3) (pair X 1 4) (X 0) k b =
      read F Q m H c (out F H k b (formed F Q D H (Ortho.move k⁻¹ ∘X) (entrants F v k b))) := by
  let W := child F Q D (Ortho.move k⁻¹ ∘X) (entrants F v k b)
  have hp := WilsonCenteredNestedDepositedField.original F Q D H m c (head v) (v 2) (pair X 2 3) (pair X 1 4) (X 0) k b
  change _ = outer F Q D H m c _ _ _ k b (restored F Q.port D (pair X 2 3) (voices (head v)) (X 1) k b) at hp
  rw [hp,child_return,apply_outer,currency,formed,cropPair]
  apply congrArg (fun w=>read F Q m H c (out F H k b w))
  unfold shadowOld
  apply congrArg (fun w=>OPE.shadow Q.port H (Ortho.move k⁻¹ ∘pair X 1 4) w (Ortho.move k⁻¹ (X 0)))
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Sigma.mk D (S.representative D (into F D k b (out F D k b W))) =
        Sigma.mk D (S.representative D W)
    rw [returns F Q]
  · refine Fin.cases ?_ (fun i=>i.elim0) j
    rfl

lemma out_sub (d:ℕ) (k:Ortho) (b:Bool) (u v:S.Field d) :
    out F d k b (u-v)=out F d k b u-out F d k b v := by cases b <;> simp [out]

/-- On this single literal orientation the signed error is the original
terminal raw tree tickets applied to their genuine output needles. -/
theorem original (D H m:ℕ) (c:Q.channels m) (X:Fin 5→E4) (v:Fin 3→S.Tag) (k:Ortho) (b:Bool) :
    read F Q m H c (restored F Q.port H (trio X) (voices v) (X 0) k b) -
      joined F Q Q.port D H m c (head v) (v 2) (pair X 2 3) (pair X 1 4) (X 0) k b =
    ∑w∈bands F.sector.derivatives H,
      scalar b (whole F Q (named (entrants F v k b)) w (Ortho.move k⁻¹ ∘X) -
        tree F Q (named (entrants F v k b)) w D (Ortho.move k⁻¹ ∘X)) *
          read F Q m H c (out F H k b (Q.port.loaded w H)) := by
  have direct : restored F Q.port H (trio X) (voices v) (X 0) k b =
      out F H k b (shadowOld Q.port H (trio (Ortho.move k⁻¹ ∘X)) ((Ortho.move k⁻¹ ∘X) 0) (voices (entrants F v k b))) := by
    rw [currency,cropTrio]
    rfl
  rw [direct,joined_return,←map_sub,←out_sub]
  erw [WilsonCenteredNestedRawDiagram.original F Q (entrants F v k b) D H (Ortho.move k⁻¹ ∘X)]
  rw [add_smul,map_sum]
  simp only [map_smul,smul_eq_mul]

end YM.Integration.WilsonCenteredNestedSharedField
