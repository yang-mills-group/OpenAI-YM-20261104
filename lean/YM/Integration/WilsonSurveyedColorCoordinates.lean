import YM.Integration.WilsonSurveyedColorBank
import YM.Integration.WilsonSurveyedColorOPE

/-! Pass the actual scale hearing to the physical MS multilinear field space.
The two books can file different dimensional representatives for the same
external field index. Every numerical component at every grade is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorCoordinates
open Function Finset
open Maxwell MS MS.Land MS.Local.Physical MS.Theater MS.Tide MS.Rake MS.Rake.Geo
open MS.High FVA2 FVA2.Register FVA2.Dframe FVA2.Scale FVA2.Scale.Equator FVA2.O FVA2.O.Score
open FVA2.Arrival FVA2.Arrival.Schedule XSpace XSpace.Structure1 XSpace.Cirrus
open WilsonSurveyedColorHearing
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {n d : ℕ}
variable {O : Booked (Press.portDeck G)} {O' : Booked (Press.portDeck G)} (M : MS_Data G O) (M' : MS_Data G O') (ν : ℝ)

def vacuum : Prop := ∀ k,
  filed U (approach (frameF Unit ν) M k) = approach (frameF Unit ν) M' k

def named (a : Rake.Label (Press.portDeck G)) (b : Rake.Label (Press.portDeck G)) : Prop := ∀ k,
  filed U (rowM (frameF Unit ν) M a k) = rowM (frameF Unit ν) M' b k

theorem printed (q q' : Fin n → Toon G d) (x : Points n) (hx : x∈conf n)
    (hV : vacuum U M M' ν) (names : ∀ j, named U M M' ν (flash (q j)) (flash (q' j))) (k : ℕ) :
    meteor ν M d x k (fill q) = meteor ν M' d x k (fill q') := by
  rw [ribbon,ribbon]
  have eqh := WilsonSurveyedColorBank.labelled U (u:=flash ∘ q) (u':=flash ∘ q')
    (track hx) ν hV names
  exact congrFun (congrFun eqh Finset.univ) k

theorem vectors (σ : Fin n → Toon G d ≃ Toon G d) (x : Points n) (hx : x∈conf n)
    (hV : vacuum U M M' ν) (names : ∀ j e, named U M M' ν (flash e) (flash (σ j e)))
    (p p' : Tags G d n)
    (coordinates : ∀ t : Fin n → Toon G d, each t p = each (fun j => σ j (t j)) p') (k : ℕ) :
    meteor ν M d x k p = meteor ν M' d x k p' := by
  rw [stencil_he (meteor ν M d x k),stencil_he (meteor ν M' d x k)]
  apply Fintype.sum_equiv (Equiv.piCongrRight σ)
  intro t
  rw [coordinates t]
  congr 1
  exact printed U M M' ν t (fun j => σ j (t j)) x hx hV (fun j => names j (t j)) k

/- In corresponding named bases the full wave, hence the output as well as
all the inputs of its canonical ordinary OPE, agrees. -/
theorem positioned (hV : vacuum U M M' ν)
    (names : ∀ a : Rake.Label (Press.portDeck G), named U M M' ν a a) :
    Equator.wave ν M = Equator.wave ν M' := by
  funext d n x k
  ext1 p
  exact vectors U M M' ν (fun _ => Equiv.refl _) x.val x.property hV
    (fun _ e => names (flash e)) p p (fun _ => rfl) k

theorem ordinaryOPE (hV : vacuum U M M' ν)
    (names : ∀ a : Rake.Label (Press.portDeck G), named U M M' ν a a)
    (u : Scan G n) (r : ℝ) :
    Canon.OPECoefficients (Equator.wave ν M) u r = Canon.OPECoefficients (Equator.wave ν M') u r := by
  rw [positioned U M M' ν hV names]

end YM.Integration.WilsonSurveyedColorCoordinates
end
