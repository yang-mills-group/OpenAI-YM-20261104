import YM.Integration.WilsonRichPrimitiveTerminal

/-! The finite signed rich-book terminal is a sum of genuine finite RG10
inversion moments on its declared period. The power restoring each primitive
is computed from the actual input frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichPrimitiveInversion
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open MS MS.Menus MS.Dial FVAAlt2 FVAAlt2.Lobby
open Pert.Orb PertExtension PertExtension.Series.Tested
open FormalOPE.RG10.InversionTop SchemeRG11.Sway
open WilsonRichPrimitiveTerminal PowerSeries
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {I : Type} [LinearOrder I] [Fintype I] (p : I → MS.Rake.Label B) {n : Side}
    (x : I → Site n) (hn : Admissible n) (c : frames R p)
local notation "z₁" => ∏ i, WilsonRichPrimitiveTerminal.gauge R p x c i
local notation "d₁" => WilsonRichPrimitiveTerminal.rank R p c

def cutoff (k : ℕ) : ℂ :=
  coeff (k+d₁) ((feed (even_iff_two_dvd.mpr hn.2)).step (vertices G n) (raw (Orb.restrictedO z₁)))

theorem finite (k : ℕ) : cutoff R p x hn c k = (Fixed.treeMom R.metals.O z₁ d₁ k : ℂ) := by
  let h := fun i : I => Shop.field_ok (R.family.localSection (p i).h) (c i)
    (R.makes.sections _) (Block.clothes R _) (x i)
  have hc (i : I) (_ : i ∈ (Finset.univ : Finset I)) :
      Continuous (WilsonRichPrimitiveTerminal.gauge R p x c i) :=
    Complex.continuous_re.comp ((R.family.localSection (p i).h).continuous_places _ _)
  have held := Fixed.preT Finset.univ hn h hc
  apply (Fixed.RG10_at Finset.univ hn h hc k).trans
  exact congrArg (fun b : ℕ → ℝ => (b (k+d₁) : ℂ))
    (Orb.chart_independent (even_iff_two_dvd.mpr hn.2) (Orb.traySpec G) R.alloy.B.ratio held.curved).1

include hn in
theorem physical : Aspiration (fun g : ℝ => g⁻¹^d₁ * Orb.preExpectation z₁ g)
    (Fixed.treeMom R.metals.O z₁ d₁) := by
  letI : Module.Free ℝ (SchemeRG11.Sway.Land G n) :=
    Module.Free.of_divisionRing ℝ (SchemeRG11.Sway.Land G n)
  let A := Module.finBasis ℝ (SchemeRG11.Sway.Land G n)
  let H := Module.finBasis ℝ (FVAAlt2.ScalarGhost G n)
  exact Fixed.preExpectation R.alloy.B.ratio A H Finset.univ hn
    (fun i : I => Shop.field_ok (R.family.localSection (p i).h) (c i) (R.makes.sections _)
      (Block.clothes R _) (x i))
    (fun i _ => Complex.continuous_re.comp ((R.family.localSection (p i).h).continuous_places _ _))

theorem closed_field :
    (∑ c : frames R p, C (charge R p c : ℂ) * PowerSeries.mk (cutoff R p x hn c)) =
      closed R p x := by
  unfold closed
  exact Finset.sum_congr rfl (fun c _ => congrArg
    (fun a : ℕ → ℂ => C (charge R p c : ℂ) * PowerSeries.mk a) (funext (finite R p x hn c)))

end YM.Integration.WilsonRichPrimitiveInversion

