import YM.Integration.WilsonRichPrimitiveRows
import YM.Integration.WilsonPhysicalExteriorFundedRows

/-! The normalized terminal series made from the original measured boxed
fields is the exact finite rich-book series. The independently issued fee
and coupling changes therefore act on the same physical primitive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichPrimitiveTerminal
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Vista MS.Fleet MS.Tide MS.Tone
open FVA2 FVAAlt2 FVAAlt2.Lobby FVAAlt2.Billing
open RegulatorIR.FVAAlt2.Lodge PertExtension PertExtension.Orb PowerSeries
open WilsonRichPrimitiveRows
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
  {I : Type} [LinearOrder I] [Fintype I] (p : I → MS.Rake.Label B) {n : Side}
  (x : I → Site n)
local notation "Reg" => basisR R
local notation "W" => warehouse R
abbrev frames := (i : I) → Lobby.JLit R.family.labels (p i)

def gauge (c : frames R p) (i : I) : Config G n → ℝ :=
  FVA2.Source.put (Plate.bare (R.family.localSection (p i).h) (c i)) (x i)

def charge (c : frames R p) : ℝ := ∏ i,(W).prices B (p i).h (p i).item.1 (p i).item.2 (c i)

def rank (c : frames R p) : ℕ := ∑ i, ((R.family.labels.level (p i).h).grades (c i)).2

/-- Both numerator and vacuum in the terminal expectation are the inversion
regulator's original ones; the readout keeps each separate Laurent shift. -/
def closed : PowerSeries ℂ := ∑ c : frames R p, C (↑(charge R p c) : ℂ) *
  PowerSeries.mk (fun k => (↑(Fixed.treeMom R.metals.O (∏ i,gauge R p x c i) (rank R p c) k) : ℂ))

theorem terminal : closed R p x = Lobby.WilsonPoint R.metals.O Reg n x p := by
  unfold closed Lobby.WilsonPoint
  refine Finset.sum_congr (by ext; simp) (fun c _ => ?_)
  apply congrArg₂ (fun a b : PowerSeries ℂ => a*b)
  · apply congrArg PowerSeries.C
    unfold charge
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun i _ => WilsonRichPrimitiveRows.price R (p i) (c i))
  · rfl

variable (Q : Prescription B) (y : ℝ) (e : ℝ)

/-- Original position and engineering normalization. Q.fees, its lower
glyphs, and its unmodified coupling substitution occur before evaluation. -/
def filed : PowerSeries ℂ := C ((e:ℂ)⁻¹ ^ wt p) *
  ∑ v : (i : I) → Glyph B (p i).h,
    (∏ i,bore p Q y i (v i)) * redo Q.team y (closed R (fun i => owner (v i)) x)

theorem normalized (he : e ≠ 0) :
    filed R p x Q y e = newEra R.metals.O Reg Q y p x e := by
  rw [Lobby.tot_cost R.metals.O Reg Q y p x e he]
  simp only [filed,Lobby.prepare,terminal]

variable {X : Type} (T : Trial X I) (u : ℝ) (k : ℕ) (z : X)
def atCut : ℂ := coeff k (filed R p (situated T z) Q (u-T.profile.θ z) (spacing T z))

theorem read : atCut R p Q T u k z = evaluateR R.metals.O Reg Q p T u k z :=
  congrArg (coeff k) (normalized R p (situated T z) Q _ _ (Real.exp_ne_zero _))

end YM.Integration.WilsonRichPrimitiveTerminal

