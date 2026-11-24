import YM.Integration.WilsonMovingForkStencilInvoice
import YM.Integration.WilsonMovingForkStencilLine
import YM.Integration.WilsonMovingForkTerminalFile

/-! An issued lower sheet supplies both the dated group field and its terminal scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilCatalogue

open Function Finset Lattice Wilson RG Source Labels Marker Trace.Pilot OPE
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open Pert.Asymptotics WilsonOriginalMixedBlockRows
open WilsonMovingForkStencilProgramme (Programme Basis piece)
open WilsonMovingForkPrintedFile (allSlots parent)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open Lattice Marker MeasureTheory
open scoped Classical
variable {G:Gauge}{R:Run G}{n K:ℕ}{d h:Fin n → ℕ}

abbrev Catalogue (R:Run G){n:ℕ}(d:Fin n → ℕ)(K:ℕ):=
  ∀(N per:ℕ)(ξ:Fin n → Site (R.family.side K per))(_q:Basis R d)(i:ℕ)(ik:i<K),
    Option (Sheet R N i (parent R ik.le per ξ))

def table (book:Catalogue R d K):Programme R d K:=
  fun N per _ ξ q i ik=>match book N per ξ q i ik with
    | some H=>board H
    | none=>WilsonMovingForkTerminalFile.quiet _

variable (book:Catalogue R d K){N per v:ℕ}
  (κ:(i:Fin n) → Knob (h i))(pt:Fin n → Chamber)(w:(i:Fin n) → R.family.label (d i))
  (ξ:Fin n → Site (R.family.side K per))
  (raw:Basis R d → (i:ℕ) → Config G (R.family.side i per) → Poly (Stock.census (Fin n)))

def Occupied (q:Basis R d)(i:ℕ)(ik:i<K):Prop:=
  ∃H:Sheet R N i (parent R ik.le per ξ),book N per ξ q i ik=some H ∧ Received H (raw q i)

theorem original (vk:v<K)
    (arrived:∀q:Basis R d,∀i, v ≤ i → (ik:i<K) → Occupied (N:=N) book ξ raw q i ik)
    (high:∀q:Basis R d,Integrable (raw q K) (Wilson.prior G _) ∧
      ∀U,(raw q K U).part (allSlots n)=((R.family.path.rep N per K).eval U:ℂ)*
        word R d κ pt (regulatorRun R.family N per K) ξ (allSlots n).val q U):
    (∀i,v ≤ i → i ≤ K → WilsonMovingForkStencilFees.At (N:=N) (table book) κ pt w ξ raw i) ∧
    (∀q:Basis R d,∀i,v ≤ i → i ≤ K → Integrable (raw q i) (Wilson.prior G _)) ∧
    ∀q:Basis R d,∃H:Sheet R N v (parent R vk.le per ξ),
      book N per ξ q v vk=some H ∧ ∀e,reading R (N:=N) (fun U=>(raw q v U).part e) v le_rfl=
        (polynomial H (regulatorRun R.family N per v)).part e:=by
  refine ⟨?_,?_,?_⟩
  · intro i vi ik
    rcases lt_or_eq_of_le ik with inside | rfl
    · apply WilsonMovingForkStencilFees.registered _ _ _ _ _ _ inside
      intro q U
      obtain ⟨H,filed,paid⟩:=arrived q i vi inside
      have selected:table book N per w ξ q i inside=board H:=by
        unfold table
        rw [filed]
      dsimp only
      rw [selected]
      exact paid.2.1 U
    · intro q
      funext U
      simpa only [numerator,WilsonMovingForkStencilProgramme.piece,allSlots,lt_irrefl,↓reduceDIte] using ((high q).2 U).symm
  · intro q i vi ik
    rcases lt_or_eq_of_le ik with inside | rfl
    · obtain ⟨_,_,paid⟩:=arrived q i vi inside
      exact paid.1
    · exact (high q).1
  · intro q
    obtain ⟨H,filed,paid⟩:=arrived q v le_rfl vk
    exact ⟨H,filed,paid.2.2⟩

end YM.Integration.WilsonMovingForkStencilCatalogue
end
