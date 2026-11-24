import YM.Integration.FVA1Physical.Wilson.RawMarker

/-! Package the all-order RG02 normalized physical mixed-source readings as a
single bank on the full first retained field, for use in a subsequent step. -/
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Lattice RG YM.Wilson Tree Precision Marker Comparison.RG02
open FVA2.CityHistory FVA2.CityHistory.Delay FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.InversionTop RGComparison.Core16
open RGComparison.Core16.Spool RGComparison.Core16.WilsonXLocal
open scoped Classical

variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V]
    (R : Census V) {m p d : ℕ} (U : V → Stamp.Reservation C (C.side (m+1) p) d)
local notation "S" => C.path.levels.clock.op m p
variable (F : Forest (C.path.levels.clock.op m p).ratio) (t : (C.path.levels.clock.op m p).Choices) (L : Bulk.Chain C.path)

def rawMarkedTicket (s : R.Mode) (q : Bool) : Ticket (Pins G (C.side m p)) :=
  if h : ∃ A : Ticket (Pins G (C.side m p)), ∀ u i,
      PowerSeries.coeff i (Stack.read u A) = rawMarker R U F t L s q u i then h.choose else 0

theorem rawMarkedTicket_eq (hC : C.Makes) (hs : ∀ i, Bid.pop (C.localSection i))
    (h : Bid.Larger (G:=G) (C.path.levels.clock.op m p)) (Z : ChartRatio G) (hZ : LocalRatio Z)
    (v : (Descent.nil (top := C.side (m+1) p)).Tags)
    (z : ℕ → PowerSeries ℝ) (hz : z 1 = 1) (s : R.Mode) (q : Bool) :
    rawMarkedTicket R U F t L s q =
      skyread Z (Descent.push S F Descent.nil) (t,v) ⟨h,True.intro⟩ z
        (exPay (look q ∘ fullProduct (MSMatch.SourceTop.field U) s.val)) := by
  let d₁ := Descent.push S F (Descent.nil (top := C.side (m+1) p))
  let J := skyread Z d₁ (t,v) ⟨h,True.intro⟩ 1
    (exPay (look q ∘ fullProduct (MSMatch.SourceTop.field U) s.val))
  have ident (u i) : PowerSeries.coeff i (Stack.read u J) = rawMarker R U F t L s q u i :=
    (raw_marker_coefficient R U hC hs F t h Z hZ v L s q u i).symm
  have ex : ∃ A : Ticket (Pins G (C.side m p)), ∀ u i,
      PowerSeries.coeff i (Stack.read u A) = rawMarker R U F t L s q u i := ⟨J,ident⟩
  have el : rawMarkedTicket R U F t L s q = J := by
    rw [rawMarkedTicket,dif_pos ex]
    apply Stack.into
    intro u
    apply PowerSeries.ext
    intro i
    exact (ex.choose_spec u i).trans (ident u i).symm
  rw [el]
  have sup : supplyZ (G:=G) d₁ Z (t,v) z = supplyZ d₁ Z (t,v) 1 := by
    simp only [d₁,supplyZ,parentZ,Pi.one_apply,hz]
  unfold J skyread premiere
  rw [sup]

end YM.Integration.FVA1Physical.Wilson
