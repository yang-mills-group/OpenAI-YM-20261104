import YM.Labels.Reference
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color

/-! Color invariance of a radial jet polynomial excludes every arity-one
basis label for a simple gauge group. The radial constraint is respected
by applying the same color endomorphism to every coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardColors
open Function Labels LinearMap
open scoped Classical
variable {G:Gauge} {j d:ℕ}

def tile (A:Taylor G j) : Module.End ℝ G.Color →ₗ[ℝ] Taylor G j where
  toFun L:=⟨fun i=>(LinearMap.toContinuousLinearMap L).compContinuousMultilinearMap (A.val i), by
    refine ⟨fun i s r=>congrArg L (A.property.1 i s r),fun z=>?_⟩
    change ∑ i : Fin 4, z i • L (Taylor.value A i z) = 0
    rw [←map_zero L,←A.radial_value z,map_sum]
    simp only [map_smul]⟩
  map_add' L M:=by apply Subtype.ext; funext i; ext1 x; rfl
  map_smul' t L:=by apply Subtype.ext; funext i; ext1 x; rfl

def dye (J:Jet G) (L:Module.End ℝ G.Color):Jet G:=fun i=>tile (J i) L

theorem self (J:Jet G):dye J LinearMap.id=J := by
  funext i; apply Subtype.ext; funext j; ext1 x; rfl

theorem rotated (u:G.El) (J:Jet G) (L:Module.End ℝ G.Color):
    dye J ((G.adjoint u).comp L)=colored u (dye J L) := by
  funext i; apply Subtype.ext; funext j; ext1 x; rfl

private def line (J:Jet G) (k:Key G): Module.End ℝ G.Color →ₗ[ℝ] ℂ :=
  Complex.ofRealCLM.toLinearMap.comp (((axes G k.1).coord k.2).comp (tile (J k.1)))

private def payout (p:Pol G) (J:Jet G):Module.End ℝ G.Color →ₗ[ℝ] ℂ :=
  ∑ a∈p.support, if h:∃k:Key G,a=Finsupp.single k 1 then
    (MvPolynomial.coeff a p) • line J h.choose else 0

private theorem counted {p:Label G d} {m:ℕ} (hp:p∈Grade (m,1))
    (J:Jet G) (L:Module.End ℝ G.Color) :
    payout p.val J L=read (dye J L) p.val := by
  classical
  unfold payout
  rw [LinearMap.sum_apply]
  conv_rhs => rw [←MvPolynomial.support_sum_monomial_coeff p.val, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have weight: Finsupp.weight bidegree a = (m,1):=
    (pure_grade _ p).1 hp (MvPolynomial.mem_support_iff.mp ha)
  rw [weight_slot] at weight
  have h:∃k:Key G,a=Finsupp.single k 1 :=
    (Finsupp.sum_eq_one_iff a).mp (congrArg Prod.snd weight)
  rw [dif_pos h]
  change MvPolynomial.coeff a p.val * coord (dye J L) h.choose =
    Labels.read _ ((MvPolynomial.monomial a) (MvPolynomial.coeff a p.val))
  rw [Labels.read,MvPolynomial.aeval_monomial]
  have degree: a.prod (fun k n=>coord (dye J L) k^n)=coord (dye J L) h.choose:=by
    conv_lhs => rw [h.choose_spec]
    simp
  rw [degree]; rfl

private def point {B:Type*} [AddCommGroup B] [Module ℝ B] (c:B→ₗ[ℝ] ℝ):
    B →ₗ[ℝ] Module.End ℝ B where
  toFun x:=c.smulRight x
  map_add' u v:=by ext x; exact smul_add (c x) u v
  map_smul' r v:=by ext x; exact smul_comm (c x) r v

private theorem invisible (simple:G.Simple) (Λ:Module.End ℝ G.Color →ₗ[ℝ] ℂ)
    (same:∀u:G.El,∀L:Module.End ℝ G.Color,Λ ((G.adjoint u).comp L)=Λ L):
    Λ LinearMap.id=0 := by
  classical
  let B:=Module.finBasis ℝ G.Color
  have zz(i:Fin (Module.finrank ℝ G.Color)):Λ.comp (point (B.coord i))=0:=by
    apply UVNext.FreeStress.no_linear simple
    intro u x
    change Λ (point (B.coord i) (G.adjoint u x)) = Λ (point (B.coord i) x)
    rw [←same u (point (B.coord i) x)]
    apply congrArg Λ
    ext1 c
    exact ((G.adjoint u).map_smul (B.coord i c) x).symm
  have decomp:(∑i,point (B.coord i) (B i))=LinearMap.id:=by
    ext1 c
    change _ = c
    rw [LinearMap.sum_apply]
    change (∑i,(B.repr c) i • B i) = c
    exact B.sum_repr c
  rw [←decomp,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact congrArg (fun L:G.Color→ₗ[ℝ] ℂ=>L (B i)) (zz i)

theorem unary_zero (simple:G.Simple) {m:ℕ} (p:Label G d) (hp:p∈Grade (m,1)):p=0:=by
  apply Subtype.ext
  apply eval_ext
  intro J
  change read J p.val=0
  calc
    _ = payout p.val J LinearMap.id := by rw [counted hp,self]
    _ = 0 := by
      apply invisible simple
      intro u L
      rw [counted hp,counted hp,rotated]
      exact p.property.2 _ u

theorem arity (simple:G.Simple) (F:Frame G d) (i:F.Index) : (F.grades i).2≠1:=by
  intro one
  have pair:F.grades i=((F.grades i).1,1):=Prod.ext rfl one
  have pure:F.basis i∈Grade ((F.grades i).1,1):=pair ▸ F.pure i
  exact F.basis.ne_zero i (unary_zero simple (F.basis i) pure)
end YM.Integration.WilsonMaxwellThermometerWardColors
