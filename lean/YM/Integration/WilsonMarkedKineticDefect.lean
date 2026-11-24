import YM.Integration.WilsonCommonConditionalGaussian
import YM.Comparison.RG02.Valence.Volume
import YM.Comparison.RG02.Adjacent.Caliber

/-! The physical change of coupling on one original marked coefficient and
the independent homogeneous kinetic change. The diagonal coefficient is
exactly one; discrepancies in the kinetic scalar act on lower orders only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedKineticDefect

open Finset Marker Multi Lattice RG Tree Wilson Exterior Precision
open Comparison.RG02 Order Adjacent Moving.Path FormalBulk08 FormalBulk08.Wine
open scoped BigOperators Classical

variable (C : Adjacent.Caliber) (cap : ℕ) (H : Wine.Pence)

/-- Original physical weight of a homogeneous rank on the reverse chart. -/
def physicalWeight (e j r : ℕ) : ℂ := motion (Adjacent.money (C.back cap) 0 j r) e

/-- The truncation is necessary: natural subtraction alone would assign
a spurious constant to higher incoming orders. -/
def formalWeight (e j r : ℕ) : ℂ :=
  if j ≤ e then (Wine.bill (Wine.bookH H) (Wine.bookU H) e j r : ℂ) else 0

theorem diagonal (e r : ℕ) : physicalWeight C cap e e r = formalWeight H e e r := by
  have hu : Wine.Fresh (Wine.bookU H) := by
    have h := congrArg (PowerSeries.constantCoeff) (Wine.book_equal H)
    have h₀ := Wine.book_fresh H
    rw [Wine.Fresh,PowerSeries.coeff_zero_eq_constantCoeff_apply] at h₀ ⊢
    simpa only [map_mul,map_one,h₀,one_mul] using h
  have hh := ((Wine.book_fresh H).pow e).mul (hu.pow r)
  simp only [physicalWeight,Adjacent.this_step,formalWeight,le_rfl,if_pos,Wine.bill,Nat.sub_self]
  exact_mod_cast hh.symm

theorem above {j e : ℕ} (he : e < j) (r : ℕ) :
    physicalWeight C cap e j r = 0 ∧ formalWeight H e j r = 0 := by
  constructor
  · rw [physicalWeight,Adjacent.triangular,if_neg (Nat.not_le.mpr he)]
  · exact if_neg (Nat.not_le.mpr he)

section
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : Adjacent.Display X) (Q : ℕ → ℕ → X → ℂ) (p : ℕ) {sizes : ℕ → ℤ}
    (bounded : Adjacent.Charge p sizes M)

include bounded

/-- The true physical reset minus the formal homogeneous sum is exactly
the lower-order change of kinetic scalar plus the transported signed
primitive discrepancy. This does not posit matching reset coefficients. -/
theorem reset (e : ℕ) (x : X) :
    Adjacent.born M (C.back cap) 0 p e x -
       ∑ j ∈ range (p+1), ∑ r ∈ range ((sizes j).toNat+1),
         formalWeight H e j r * Q j r x =
    (∑ j ∈ range (p+1), ∑ r ∈ range ((sizes j).toNat+1),
      physicalWeight C cap e j r * (Assembly.jet (M j) r x - Q j r x)) +
    ∑ j ∈ range (p+1), ∑ r ∈ range ((sizes j).toNat+1),
      (physicalWeight C cap e j r - formalWeight H e j r) * Q j r x := by
  rw [Adjacent.message (U:=M) (K:=C.back cap) (d:=0) (r:=p) bounded,
    ←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro r _
  unfold physicalWeight
  ring

end
section
variable {G : Gauge} {c s : Side} {S : StepData c s} {cut : Clip} {A : PathData G} {o : ChartRatio G}
    {V : Type} [DecidableEq V] [Fintype V] {I : Census V}
    (K : Bulk.Kernel S cut A o) (F : Forest S.ratio) (t : S.Choices)
    (menu : Bulk.Colors I G s) (v : V) (p : ℕ)

/-- The homogeneous degrees required by the reset formula are supplied by
the original physical marked kernel. The incoming degree bound uses the
power of the submitted mark and is independent of the observing field. -/
theorem measured (Q : ℕ → ℕ → fieldDir G c 1 → ℂ) (e : ℕ) (x : fieldDir G c 1) :
    let M := fun j b => (Order.observe I p (Order.logMarked (Bulk.Fk K F t menu b p)) j).part (I.fire v)
    let d := fun j : ℕ => j + menu.power (Valence.ribbon v)
    Adjacent.born M (C.back cap) 0 p e x -
       ∑ j ∈ range (p+1), ∑ r ∈ range (d j+1), formalWeight H e j r * Q j r x =
    (∑ j ∈ range (p+1), ∑ r ∈ range (d j+1),
      physicalWeight C cap e j r * (Assembly.jet (M j) r x - Q j r x)) +
    ∑ j ∈ range (p+1), ∑ r ∈ range (d j+1),
      (physicalWeight C cap e j r - formalWeight H e j r) * Q j r x := by
  intro M d
  have pay : Adjacent.Charge p (fun j => (d j : ℤ)) M := fun j _ =>
    Valence.solo K F t menu v j
  simpa only [Int.toNat_natCast] using reset C cap H M Q p pay e x

end
end YM.Integration.WilsonMarkedKineticDefect

