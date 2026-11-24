import YM.Integration.WilsonThermometerPositionInversionCoefficient
import YM.Integration.WilsonPositionProgramPeriodicLeaf

/-! The signed compact reading on an independently placed finite array. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramSignedFace
open Finset Lattice Wilson RG PertExtension Orb XSpace PhysicalNext.Repeat.Legato
open WilsonThermometerPositionInversionWords WilsonThermometerPositionInversionCoefficient
open PowerSeries
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) (p : XSpace.Period) {V : Type} [Fintype V] [LinearOrder V]
  (d : V → ℕ) (z : V → Cover) (g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t : V → ℂ)
local notation "o" => wrap p.side ∘ z
local notation "tests" => fun j (_ : Unit) => t j
local notation "E" => WilsonThermometerInversionFaces.series R d (o) g τ v (tests) ()

def reading (k : ℕ) : ℂ := ↑(E Complex.reCLM k)+Complex.I*↑(E Complex.imCLM k)

def leaf (b : Basis R d) (tree : p.Tree) :=
  WilsonPositionProgramCopyTop.normalized R p (fun j : ↥(occupied R d b) => d j.val)
    (fun j => z j.val) (axisOf R d b) tree

/-- Each occupied site may have its own genuine periodic lift. The original
native labels are used in both the physical coefficient and the formal array. -/
theorem original (tree:p.Tree) (k : ℕ) :
    reading R p d z g τ v t k =
      ∑ b : Basis R d, amplitude R d g τ v (tests) () b *
        coeff (k+WilsonThermometerPositionInversionWords.grade R d b) (leaf R p d z b tree) := by
  have ri := WilsonThermometerPositionInversionCoefficient.original R d p (o) g τ v (tests) () Complex.reCLM tree k
  have ii := WilsonThermometerPositionInversionCoefficient.original R d p (o) g τ v (tests) () Complex.imCLM tree k
  unfold reading
  rw [ri,ii]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro b _
  have lifted : leaf R p d z b tree = sheet R d p (o) b tree :=
    WilsonPositionProgramPeriodicLeaf.original R p (fun j : ↥(occupied R d b) => d j.val)
      (axisOf R d b) (fun j => z j.val) (fun j => lift ((o) j.val))
      (fun j => by simp only [Function.comp_apply,Lattice.wrap_lift]) tree
  rw [lifted]
  let O := point R d p (o) b
  have h : PreTest O := WilsonPositionProgramCopyTop.allowed R p
    (fun j : ↥(occupied R d b) => d j.val) (fun j => lift ((o) j.val)) (axisOf R d b)
  have eqn : sheet R d p (o) b tree = PowerSeries.map Complex.ofRealHom (PowerSeries.mk (Orb.diag (restrictedO O))) :=
    YM.FVA2.XPos.genuine_X tree h
  rw [eqn,PowerSeries.coeff_map,coeff_mk]
  let a := amplitude R d g τ v (tests) () b
  change ↑a.re * _ + Complex.I * (↑a.im * _) = a * _
  rw [← mul_assoc,← add_mul]
  congr 1
  exact (by rw [mul_comm Complex.I,Complex.re_add_im])
end YM.Integration.WilsonPositionProgramSignedFace
