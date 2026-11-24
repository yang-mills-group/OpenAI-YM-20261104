import YM.Integration.WilsonFactoryReportingBox
import YM.Pert.Lattice.Lifts
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon

/-! Independent posted physical glyphs span the comparator after equation
reduction. At a bare finite regulator the exact remaining polynomial is
retained, together with its actual engineering height and original frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryOnShellGlyphs
open Function Finset Labels Maxwell MS MS.Theater MS.Menus MS.Local.Physical
open FVA2 FVAAlt2 RG PhysicalNext.Repeat.Legato PertExtension PertExtension.LatticePT
open scoped Classical BigOperators
variable {G : Gauge} (B : Deck G) (d : ℕ)

def primitive (q : Glyph B d) : Label G d :=
  raiseLabel G (Nat.le_of_lt_succ q.1.isLt) (Shop.seat B q.2.2)

def spectrum : Label G d →ₗ[ℂ] (Glyph B d → ℂ) :=
  (Daylight B d).equivFun.toLinearMap.comp (observable G d).rangeRestrict

def recombine (p : Label G d) : Label G d :=
  ∑ q : Glyph B d, spectrum B d p q • primitive B d q

def unpaid (p : Label G d) : Label G d := p - recombine B d p

theorem glyph (q : Glyph B d) :
    observable G d (primitive B d q) = (Daylight B d q).val := by
  rw [readHeight]
  rfl

theorem measure (p : Label G d) : observable G d (recombine B d p) = observable G d p := by
  let a : shellSector G d := (observable G d).rangeRestrict p
  have hr := (Daylight B d).sum_repr a
  unfold recombine
  rw [map_sum]
  simp only [map_smul,glyph]
  have hh := congrArg (shellSector G d).subtype hr
  rw [map_sum] at hh
  simp only [map_smul] at hh
  exact hh

theorem equation (p : Label G d) : unpaid B d p ∈ equationIdeal G d := by
  change observable G d (p - recombine B d p) = 0
  rw [map_sub,measure,sub_self]

theorem registered (L : Frames G) (p : Label G d) :
    Pert.RawLabels.enroll L d p =
      ∑ q : Glyph B d, spectrum B d p q • Pert.RawLabels.enroll L d (primitive B d q) := by
  have h := (Pert.RawLabels.enroll_eq L (p:=p) (q:=recombine B d p)).mpr (measure B d p).symm
  simpa only [recombine, map_sum,map_smul] using h

/-- Every arbitrary measured comparator field, at its real original domain,
as a genuinely prescribed independent physical deck expansion. -/
theorem comparator (L : Frames G) (a : (Maxwell.freeTable L).Field d) :
    a = ∑ q : Glyph B d, spectrum B d (Pert.RawLabels.physicalLabel L d a) q •
      Pert.RawLabels.enroll L d (primitive B d q) := by
  exact (Pert.RawLabels.physical_round L a).symm.trans (registered B d L _)

variable (R : Run G)
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "T" => topMatrix S R.family.params (R.makes.sections d) (Block.clothes R d)

def prices : (F).Coeff →ₗ[ℂ] (Glyph B d → ℂ) :=
  (spectrum B d).comp ((F).coords.symm.toLinearMap.comp ((T).conversion (covarianceSymbol G)).toLinearMap)

theorem source (c : (F).Coeff) : prices B d R c = spectrum B d (WilsonFactoryBoxedFields.label R d c) := rfl

def fare : ℝ := ∑ i : (F).Index,∑ q : Glyph B d,‖prices B d R (Pi.single i 1) q‖

/-- Finite original basis price on arbitrary complex coefficients; independent
of both periods, reporting windows and the two actual lifted test fields. -/
theorem bounded (c : (F).Coeff) :
    ∑ q : Glyph B d,‖prices B d R c q‖ ≤ (F).coeffSize c * fare B d R := by
  have hc : c = ∑ i : (F).Index,c i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply,mul_ite]
  calc
    _ = ∑ q : Glyph B d, ‖∑ i : (F).Index,c i * prices B d R (Pi.single i 1) q‖ := by
      conv_lhs => rw [hc]
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    _ ≤ ∑ q : Glyph B d,∑ i : (F).Index, ‖c i‖ * ‖prices B d R (Pi.single i 1) q‖ := by
      exact sum_le_sum fun q _ => (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ _ := by
      rw [sum_comm]
      simp_rw [←mul_sum]
      unfold Frame.coeffSize
      rw [Finset.sum_mul]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (single_le_sum
        (f:=fun h : (F).Index => ∑ q : Glyph B d, ‖prices B d R (Pi.single h 1) q‖)
        (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ i)) (norm_nonneg _)

end YM.Integration.WilsonFactoryOnShellGlyphs
