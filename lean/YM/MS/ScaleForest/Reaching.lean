import YM.MS.ScaleForest.AllHistories
import YM.MS.ScaleForest.Optics
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionExternalMSRecursion

/-!
# Identify the independently computed Laurent and finite kernels

Applies with the books and their actual representatives, also with the
standard constructors. The angular dimensional integration at higher dimensions is the one
in these books and kernels. In particular no diagonal scalar-only test of
polarizations is assumed. All the choices of color convention, i factors and field/superfield
order are held in the respective kernel operands throughout.

Left sides (in the equalities) are from the UV-cutoff limit and all admissible
scale-ordered Feynman forest subtractions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Mach Halo Emit Local.Physical
open Land Outlook
open FVA2.Position FVA2.Position.OpenAxis WilsonMS
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {D : Deck G} {A : Land.Booked D}

abbrev markVertex (A : Land.Booked D) (h : ℕ) (v : Plaid D h) : T (LocalVertex G false h) := fun n=> label A v n

variable (P : Palette G)
def marksOn (A : Land.Booked D) (h : ℕ) (v : Plaid D h) : T (Flats G) := atMark P (markVertex A h v)
def polesOn (A : Land.Booked D) (h : ℕ) (v : Plaid D h) : T (Coat G) := markPoles P (markVertex A h v)

theorem comet_label (A : Land.Booked D) (h : ℕ) (v : Plaid D h) : comet h 0 (bulkSeries P)
    (gloss (Literal.linear (Mob G) (A.optics h v))) (marksOn P A h v) (polesOn P A h v) :=
  computes_mark P (markVertex A h v)

theorem germ_bulk (F : MS_Data G A) : bulkPoles P = F.poleS ∧ ∀ n, Pact (bulkSeries P n) (F.bulk n) :=
  original_external_bulk_germ F (calculates_bulk P)

theorem germ_ones (F : MS_Data G A) (h : ℕ) (v : Plaid D h) : polesOn P A h v = F.poles h v ∧
    ∀ n, Pact (marksOn P A h v n) (F.marks h v n) := original_external_marked_germ F (calculates_bulk P) h v (comet_label P A h v)

variable (F : MS_Data G A)

def graph_data (A : Land.Booked D) : Land.MS_Data G A where
  bulk := bulkSeries P
  marks := marksOn P A
  poleS := bulkPoles P
  poles := polesOn P A
  bulkOK := calculates_bulk P
  markOK := comet_label P A

theorem graph_order_zero (P : Palette G) : bulkSeries P 0=0 := (calculates_bulk P 0).2 rfl

theorem reached_bulk : Outlook.Archive 4 (bulkSeries P)=Archive 4 F.bulk := by
  funext n ⟨y,s⟩
  have he := Lift.unique (f:=Parade (F.bulk n) 4 y s) (Lift.congr (Rub (gang (bulk_path P n)|>.dost y s) 0)
    (prom ((germ_bulk P F).2 n) 4 s y)) (Rub (gang (F.bulkOK n)|>.dost y s) 0); exact congr_fun he 0

theorem reached_at (d : ℕ) (v : Plaid D d) : Archive d (marksOn P A d v)=Archive d (F.marks d v) := by
  funext n ⟨y,s⟩
  have he := Lift.unique (f:=Parade (F.marks d v n) d y s) (Lift.congr (Rub (gang (comet_label P A d v n)|>.dost y s) 0)
    (prom ((germ_ones P F d v).2 n) d s y)) (Rub (gang (F.markOK d v n)|>.dost y s) 0); exact congr_fun he 0

/-- Applied endpoints on the calibrated pair of native data. Both
use the SAME graph sums, without recalculating any label. -/
theorem aligned (T : MS_Data G (OpenAxis.Plot (FVA2.Press.portDeck G))) (F : MS_Data G (JRad.book G))
    (v : Plaid (FVA2.Press.portDeck G) h) :
    let A := OpenAxis.Plot (FVA2.Press.portDeck G)
    let w : Plaid (Ensure.deck G) h := (Integration.FVA1Physical.Exchange.continuumLimit_deck G) ▸ v
    bulkPoles P = F.poleS ∧ bulkPoles P=T.poleS ∧
      polesOn P A h v=T.poles h v ∧ polesOn P A h v=F.poles h w ∧
      ∀ n, Pact (bulkSeries P n) (F.bulk n) ∧ Pact (bulkSeries P n) (T.bulk n) ∧
        Pact (marksOn P A h v n) (T.marks h v n) ∧ Pact (marksOn P A h v n) (F.marks h w n) := by
  intro A w; obtain hx:= across_decks T F v; dsimp only at hx
  obtain ⟨he,hE⟩:=germ_bulk P F; obtain ⟨hp,hP⟩:=germ_bulk P T; obtain ⟨ht,hT⟩:= germ_ones P T h v
  exact ⟨he,hp,ht,ht.trans hx.1,fun n=>⟨ hE n,hP n,hT n,pact_comp (hT n) (hx.2 n) ⟩⟩

theorem unchanged_palette (V : Palette G) :
    bulkPoles P=bulkPoles V ∧ (∀ i,Pact (bulkSeries P i) (bulkSeries V i)) ∧
    ∀ (h : ℕ) (W : T (LocalVertex G false h)), markPoles P W= markPoles V W ∧ ∀ i, Pact (atMark P W i) (atMark V W i) := by
  obtain ⟨hp,hv⟩:= unique_B (calculates_bulk P) (calculates_bulk V)
  exact ⟨hp,hv,fun h W=> unique_M (computes_mark P W) (computes_mark V W) hv⟩
end YM.MS.ScaleForest
