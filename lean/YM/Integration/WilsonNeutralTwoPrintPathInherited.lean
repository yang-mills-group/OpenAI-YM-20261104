import YM.Integration.WilsonNeutralTwoPrintPathRebadge
import YM.Integration.WilsonReceivedDepositedOrbitalPages

/-! An already deposited connected subword can be used as a single new mark
at any copied site while retaining its original tested internal addresses. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathInherited
open Function Finset Filter Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e d:ℕ}

def atom (Y:Outerm G D)(k:I→ℕ)(e:ℕ)(y:I → Cover)(J:Finset I)(c:I)
    (read:Pen D J →L[ℝ] Vote d):TowerS G d:=
  tuftV read (shifted ((submit Y k e) y J) (-(y c)))

private theorem center {α V:Type}[NormedAddCommGroup V]{r:ℕ}{s B:ℝ}
    (p:Cover)(K:Ten V (Cloth α) r)(h:Cork Bank.terrain p s B K):
    Cork Bank.terrain 0 s B (revolve (-p) K):=by
  refine ⟨h.1,?_⟩
  intro x
  have q:=h.2 (jog (-(-p)) ∘ x)
  rw [←rev_league (-p) (fun x y=>by simp [Bank.terrain]),neg_add_cancel] at q
  exact q

omit [DecidableEq I] in
theorem posted (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(hB:1 ≤ B)
    (cover:CoverBill Y e s B)(y:I → Cover)(J:Finset I)(c:I)(live:c∈J)
    (read:Pen D J →L[ℝ] Vote d):
    Auth (mass k J) (atom Y k e y J c read) ∧
      ∀a,a ≤ e → ∀r,Cork Bank.terrain 0 s (‖read‖*B^J.card)
        ((atom Y k e y J c read).2 a r):=by
  have copies:=WilsonReceivedCompactVerseEntrance.original Y well hs hB cover
  refine ⟨((copies.2.1.level' y J).shifted _).tuft _,?_⟩
  intro a ha r
  have C:=(cover y J a ha r).to_cork hs.le live
  rw [←(copies.2.2.1 y J a ha).1] at C
  exact (center (y c) _ C).touch read

end YM.Integration.WilsonNeutralTwoPrintPathInherited
end
