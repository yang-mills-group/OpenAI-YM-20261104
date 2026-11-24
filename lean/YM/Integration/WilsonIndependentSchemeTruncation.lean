import YM.FVA2.Main
import YM.RG11Proof.Jets.Subst
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

/-! Finite polynomial compositions of the independently prescribed MS position
scheme. Their first neglected power is controlled algebraically, irrespective
of whether the infinite formal power series converges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentSchemeTruncation

open Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land RG11.Jets
open scoped Polynomial

def finite (p : ℕ) (a : PowerSeries ℂ) : ℂ[X] := PowerSeries.trunc (p+1) a

private theorem retained (p : ℕ) (a : PowerSeries ℂ) :
    Through p ((finite p a : ℂ[X]) : PowerSeries ℂ) a := by
  intro i hi
  rw [Polynomial.coeff_coe,finite,PowerSeries.coeff_trunc,if_pos (by omega)]

private theorem insert_polynomial (a b : ℂ[X]) (zero : Anchored (a : PowerSeries ℂ)) :
    PowerSeries.subst (a:PowerSeries ℂ) (b:PowerSeries ℂ) = (↑(b.comp a) : PowerSeries ℂ) := by
  rw [PowerSeries.subst_coe zero.permits]
  induction b using Polynomial.induction_on' with
  | add f h hf hh => simp [hf,hh]
  | monomial j z => simp

theorem composed (p : ℕ) (outer inner : PowerSeries ℂ) (root : Anchored inner) :
    (Polynomial.X : ℂ[X])^(p+1) ∣
      (finite p outer).comp (finite p inner) - finite p (PowerSeries.subst inner outer) := by
  have inner0 : Anchored ((finite p inner : ℂ[X]):PowerSeries ℂ) := (retained p inner).head.trans root
  have composed := Through.compose (retained p outer) (retained p inner) inner0
  rw [insert_polynomial _ _ inner0] at composed
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  rw [Polynomial.coeff_sub, sub_eq_zero]
  have eq := (composed.trans (retained p (PowerSeries.subst inner outer)).symm) i (by omega)
  simpa only [Polynomial.coeff_coe] using eq

private theorem paid_pair (p : ℕ) {a b : PowerSeries ℂ} (pay : Reg.Token.Payment a b) :
    ((Polynomial.X : ℂ[X])^(p+1) ∣ (finite p a).comp (finite p b) - finite p PowerSeries.X) ∧
    ((Polynomial.X : ℂ[X])^(p+1) ∣ (finite p b).comp (finite p a) - finite p PowerSeries.X) := by
  have b0 : Anchored b := (PowerSeries.coeff_zero_eq_constantCoeff_apply b).symm.trans pay.own
  have a0 : Anchored a := (PowerSeries.coeff_zero_eq_constantCoeff_apply a).symm.trans pay.launch
  have left := composed p a b b0
  have right := composed p b a a0
  rw [pay.right] at left
  rw [pay.left] at right
  exact ⟨left,right⟩

variable {G : Gauge} {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)

include M in
theorem inverse (ν : ℝ) (p : ℕ) :
    let c := Measure.chi Z.criterion ν T
    let f := Measure.f Z.criterion ν T
    let id := finite p (PowerSeries.X : PowerSeries ℂ)
    ((Polynomial.X : ℂ[X])^(p+1) ∣ (finite p c).comp (finite p f) - id) ∧
    ((Polynomial.X : ℂ[X])^(p+1) ∣ (finite p f).comp (finite p c) - id) :=
  paid_pair p (M.positionCoupling ν).2

end YM.Integration.WilsonIndependentSchemeTruncation

