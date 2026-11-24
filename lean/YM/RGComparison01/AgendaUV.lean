import YM.RGComparison01.AgendaFlora
import YM.UVExtension.Reports.Ultraviolet
import YM.EveryPhase.Extension

/-!
# Payable analytic demands and the common witness

 Output includes EXACTLY the conclusions of
 `checks.ComparisonCommonWitness` on chosen C, f, F and phase, with also
 paid extra costs; `RichFloral.forget` upgrades compatible purchase to the
 unqualified premise. No identification with independently chosen C made
 elsewhere. For simultaneous use pick with Agenda of ALL the additional
 demands and attend other choices in their proper before-L, delay, etc order.
 Analytic-price instances separate. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
variable {G : Gauge}
open Filter
open UVExtension

/-- Joint constructor, when potential costs are payable. -/
theorem withAgenda {Ω : Agenda G} (H : Ω.Payable) (hG : G.Simple) (penalty : ℝ) (hp : 0 < penalty) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book)
      (F : Spec.Final C f T) (L : EveryPhase.Almanac F),
      Oasis.RichFloral (hG := hG) Ω C ∧ C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = penalty ∧
      Oasis.Floral (hG := hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed F L := by
  obtain ⟨C,hM,hC,F,hW,hs,hQ,hR⟩ := Oasis.fruitionRich H hG penalty hp
  obtain ⟨f,T,_,_,⟨B⟩⟩ := hR Extraction.Order.full
  obtain ⟨V,hV⟩ := EveryPhase.all_characters B
  exact ⟨C,_,T,B,V,F,hM,hC,hW,F.forget,Reports.useFull F.forget ⟨B⟩,hQ,hV⟩
end YM.RGComparison01
