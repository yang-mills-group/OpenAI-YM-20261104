import YM.Integration.WilsonNeutralColumnComparison
import YM.Trace.Physicalv2.GermPrices
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Factory

/-! Exact two-endpoint conversion between the filed fourth-horizon
coordinates and the intrinsic flat-germ reading of the complete
physical returning singleton. The gallery, cutoff and period agree at
the two ends. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralPhysicalGerm
open Filter Wilson RG Source PhysicalNext.Repeat.Legato
open Trace.Physical.GermGraph WilsonNeutralGradeFourTransport
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {N p : ℕ}
local notation "C" => R.family
local notation "F" => R.family.labels.level 4
local notation "V" => R.family.label 4

def reader (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) : V ≃ₗ[ℂ] V :=
  (atDate R (p:=p) i h.post hi).symm.trans <|
    (R.family.factory 4 N p).terminal.symm.trans <| (fitting 4 N p i R.makes h hi).trans
      (LinearEquiv.smulOfNeZero ℂ V ((R.family.S.a i:ℂ)^4)⁻¹
        (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos i).ne'))))

theorem projected (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) (z : V) :
    reader R i h hi (atDate R (p:=p) i h.post hi z) =
      ((R.family.S.a i:ℂ)^4)⁻¹ • page 4 p i ((R.family.factory 4 N p).entries i ((R.family.factory 4 N p).terminal.symm z)) := by
  simp only [reader,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rfl

/-- The two engineering normalizations cancel in the physical reader.
Its right side is the original WilsonPhysicalProjectionColumns.correction
given on the stored, unscaled factory. -/
theorem native (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) :
    reader R i h hi = (MultiNext.SignedSource.matrices R.makes h.post hi p).symm.trans
      (fitting 4 N p i R.makes h hi) := by
  ext x : 1
  obtain ⟨z,rfl⟩ := (atDate R (p:=p) i h.post hi).surjective x
  let w := (R.family.factory 4 N p).terminal.symm z
  let a : ℂ := ((R.family.S.a i:ℂ)^4)⁻¹
  have stored : atDate R (p:=p) i h.post hi z =
      a • MultiNext.SignedSource.matrices R.makes h.post hi p w := rfl
  rw [projected R i h hi,stored]
  let M := MultiNext.SignedSource.matrices R.makes h.post hi p
  let T := fitting 4 N p i R.makes h hi
  change a • T w = T (M.symm (a • M w))
  rw [M.symm.map_smul,M.symm_apply_apply,T.map_smul]

private theorem salary (c : ℂ) (x : V) : (F).coeffSize (c•x)=‖c‖*(F).coeffSize x := by
  simp only [Labels.Frame.coeffSize,Pi.smul_apply,norm_smul,Finset.mul_sum]

/-- Only the relative price of the physical graph enters this estimate.
It is uniform before either regulator and holds on the full horizon. -/
theorem prices (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) (x : V) :
    (F).coeffSize (reader R i h hi x) ≤ 2*(F).coeffSize x ∧
    (F).coeffSize x ≤ 2*(F).coeffSize (reader R i h hi x) := by
  obtain ⟨z,rfl⟩ := (atDate R (p:=p) i h.post hi).surjective x
  let w := (R.family.factory 4 N p).terminal.symm z
  have fee := size_gap 4 N p i R.makes h hi w
  let a : ℂ := ((R.family.S.a i:ℂ)^4)⁻¹
  let Z := (R.family.factory 4 N p).entries i w
  have posted : atDate R (p:=p) i h.post hi z = a • Z.x := rfl
  have heard : reader R i h hi (atDate R (p:=p) i h.post hi z) =
      a • page 4 p i Z := projected R i h hi z
  rw [heard,posted]
  simp only [salary]
  constructor
  · exact (mul_le_mul_of_nonneg_left fee.1 (norm_nonneg a)).trans_eq (mul_left_comm _ _ _)
  · exact (mul_le_mul_of_nonneg_left fee.2 (norm_nonneg a)).trans_eq (mul_left_comm _ _ _)

/-- The actual physical unit has zero regular-error allowance. This
fixes its intrinsic germ exactly at every eligible cutoff and date. -/
theorem unit (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) :
    reader R i h hi (F).e0=(F).e0 := by
  let w := (R.family.factory 4 N p).terminal.symm (R.family.refUnit 4)
  let Z := (R.family.factory 4 N p).entries i w
  have entry : Z.x = unitVec (F) R.family.path i := Trace.Terrace.nib_unit R.family R.makes h.post hi
  have empty : (F).core (F).e0=0 := by
    funext b
    by_cases b0 : b=0 <;> simp [Labels.Frame.core,Labels.Frame.e0,Function.update,b0]
  have quiet : (F).core Z.x = 0 := by rw [entry,unitVec,map_smul,empty,smul_zero]
  have issuer := R.makes.calibrated 4 N p (h.post.trans hi)
  have inc := issuer.cap i h.post hi w
  change Z.remBound 0 (R.family.path.rep N p i) (safety R.family i)
    ((R.family.path.levels.params i).columns*(F).coeffSize ((F).core Z.x)) at inc
  rw [quiet] at inc
  have group : reads 4 N p i Z 0 := ⟨issuer.format i h.post hi w,by
    simpa only [Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using inc⟩
  have debt := measured_diff 4 N p i R.makes h.post hi group
  rw [mul_zero] at debt
  have zero : page 4 p i Z=Z.x :=
    sub_eq_zero.mp <| norm_eq_zero.mp <| le_antisymm
      ((Push.Local.norm_le_size (F) (page 4 p i Z-Z.x)).trans debt) (norm_nonneg _)
  have v := projected R i h hi (R.family.refUnit 4)
  change reader R i h hi (atDate R (p:=p) i h.post hi (R.family.refUnit 4)) =
    ((R.family.S.a i:ℂ)^4)⁻¹ • page 4 p i Z at v
  rw [zero] at v
  change reader R i h hi (atDate R (p:=p) i h.post hi (R.family.refUnit 4)) =
    atDate R (p:=p) i h.post hi (R.family.refUnit 4) at v
  rwa [atDate_unit] at v

theorem map_scalars (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) :
    (scalars R).map (reader R i h hi).toLinearMap=scalars R := by
  rw [scalars,Submodule.map_span,Set.image_singleton]
  exact congrArg (fun x : V => Submodule.span ℂ ({x}:Set V)) (unit R i h hi)

def quotientReader (i : ℕ) (h : Opened C 4 i p) (hi : i ≤ N) :
    (V ⧸ scalars R) ≃ₗ[ℂ] (V ⧸ scalars R) :=
  Submodule.Quotient.equiv _ _ _ (map_scalars R i h hi)

/-- The actual two-endpoint conjugation of a finite independent response
given on the intrinsic panels. Its input is the physical upper column. -/
def submitted {i : ℕ} (prev : Opened C 4 i p) (next : Opened C 4 (i+1) p) (live : i<N)
    (M : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  (reader R i prev live.le).symm.toLinearMap.comp <|
    M.comp (reader R (i+1) next live).toLinearMap

/-- A signed comparison on the actual intrinsic singleton of one of the
two thermometer legs already pays its lower-file defect. Both direction
changes use the original physical graph. -/
theorem signed {i : ℕ} (prev : Opened C 4 i p) (next : Opened C 4 (i+1) p) (live : i<N)
    (A : Group C 6) (leg : Fin 2) (M : V →ₗ[ℂ] V) (c : ℝ) :
    let x : ℕ → V := fun j => coordinates R A j N p leg.succ
    (F).coeffSize (M (reader R (i+1) next live (x (i+1)))-reader R i prev live.le (x i))≤c →
      (F).coeffSize (submitted R prev next live M (x (i+1))-x i)≤2*c := by
  intro x cost
  have cross := (prices R i prev live.le (submitted R prev next live M (x (i+1))-x i)).2
  erw [map_sub,LinearEquiv.apply_symm_apply] at cross
  exact cross.trans (mul_le_mul_of_nonneg_left cost zero_le_two)

theorem connected {i : ℕ} (prev : Opened C 4 i p) (next : Opened C 4 (i+1) p) (live : i<N)
    (A : Group C 6) (leg : Fin 2) (M : V →ₗ[ℂ] V) (c : ℝ) :
    let x : ℕ → V := fun j => coordinates R A j N p leg.succ
    (F).coeffSize (M (reader R (i+1) next live (x (i+1)))-reader R i prev live.le (x i))≤c →
      ‖(scalars R).mkQ (submitted R prev next live M (x (i+1))-x i)‖≤2*c := by
  intro x cost
  let z := submitted R prev next live M (x (i+1))-x i
  exact ((Submodule.Quotient.norm_mk_le (scalars R) z).trans (Push.Local.norm_le_size (F) z)).trans
    (signed R prev next live A leg M c cost)

/-- The physical graph and its two quantitative inequalities are
available at both dates, eventually in the common reporter before p,N. -/
theorem original (simple : G.Simple) : ∀ᶠ i : ℕ in atTop, ∀ p,
    Opened C 4 i p ∧ Opened C 4 (i+1) p := by
  have h := open_late C simple 4
  filter_upwards [h,(tendsto_add_atTop_nat 1).eventually h] with i lower upper p
  exact ⟨lower p,upper p⟩

end YM.Integration.WilsonNeutralPhysicalGerm
