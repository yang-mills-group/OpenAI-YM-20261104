import YM.XSpace.OnShell
import YM.XSpace.Compat.MaxwellBidegree
import YM.XSpace.WickOperator
import YM.Next.MAXWELL.System

/-!
# A compatible choice of section of the **free** equation ideal

Address-zero, bidegree, real, equivariant. Use invariant-complement freedom in §g0; no
metric fixed for this finite-dimensional lift. (As usual can think of using orthogonal
complements by taking metrics with summands in a real invariant splitting orthogonal.)
Here too choosing an algebra hom (also on the ancillary NON-invariant linear slots) is very
useful. Apply to color-invariant Maxwell Wick labels. Filtration interpreted by inclusions;
no changing the representation with perturbative order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.On
open Function Filter Set Maxwell Maxwell.Free Source Labels MvPolynomial
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
section legs
variable (G : Gauge) (j : ℕ)


variable {G j}
end legs



variable {d n l : ℕ}


-- on grade (engineering only)
def Grade (G : Gauge) (d : ℕ) := shellSector G d ⊓ MvPolynomial.weightedHomogeneousSubmodule ℂ Free.scaleW d

instance finite (d : ℕ) : FiniteDimensional ℂ (Grade G d)  := by
  letI : FiniteDimensional ℂ (shellSector G d):= by unfold shellSector; infer_instance
  exact FiniteDimensional.of_injective (Submodule.inclusion (show Grade G d ≤ shellSector G d from inf_le_left)) (Submodule.inclusion_injective _)

/-- bare top normalized columns at OWN horizons. -/
def stencil (H : Hol G) (S : Survey G H d) (P : Period) (T : P.Tree) (x : P.Sites) :
    (Grade G d) →ₗ[ℂ] Bare.Series T G:= Bare.column T S x ∘ₗ sectionMap d ∘ₗ Submodule.inclusion (show Grade G d≤shellSector G d from inf_le_left)

lemma stencil_unit {H : Hol G} (S : Survey G H 0) (P : Period) (T : P.Tree) (x : P.Sites) (e : Grade G 0) (he:e.val=1):
    stencil H S P T x e=1:=by
  generalize hv : (Submodule.inclusion (show Grade G 0 ≤ shellSector G 0 from inf_le_left) e)= z
  change Bare.column T S x (sectionMap 0 _) = 1; rw [hv,show sectionMap 0 z=unit G 0 from Subtype.ext ?_, Bare.column_unit]; rw [section_value,← hv]; change lifting e.val= 1; rw [he,map_one]
end YM.XSpace.On
