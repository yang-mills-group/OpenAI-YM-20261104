import YM.Integration.WilsonFactoryBoxedFields
import YM.Integration.WilsonOrdinaryObservedChart
import YM.RG17.Gathers

/-! The two true physical quotient fields have independent finite factory
lifts on the selected reporting chart. Their reporting entries are exact,
and their original positive group-field readings use the boxed sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryReportedChart
open Function Filter Lattice Wilson RG Spec OPE SharpGram RG12 RG17 Source PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (L : Layout F)
local notation "C₀" => R.family

/-- Finite, rather than subsequential, cancellation of the two original
charts at the reporting level. -/
theorem head (d k : ℕ) (h : (C₀).ref d ≤ k) (j : UVIndex) (hj : k ≤ j.1) (v : (C₀).label d) :
    (((C₀).factory d j.1 j.2).entries k (((C₀).factory d j.1 j.2).terminal.symm
      (atK C₀ F.room.cutoff d k j v))).x = v := by
  have sold := (RG12.charts C₀ F.room.cutoff d k j).apply_symm_apply v
  rw [RG12.charts,dif_pos ⟨h,hj⟩] at sold
  change (((C₀).factory d j.1 j.2).entries k (((C₀).factory d j.1 j.2).terminal.symm
    ((RG12.charts C₀ F.room.cutoff d k j).symm v))).x = v
  rw [RG12.charts,dif_pos (show (C₀).ref d ≤ k ∧ k ≤ j.1 from ⟨h,hj⟩)]
  exact sold

def lift (d : ℕ) (r : ℝ) (v : (C₀).label d) :=
  (L.shift d r).symm (((((C₀).S.a (L.level r))^d : ℝ) : ℂ)⁻¹ • v)

theorem at_radius (d : ℕ) (r : ℝ) (j : UVIndex) (v : (C₀).label d) :
    RG17.atRef L d r j (lift R F L d r v) = atK C₀ F.room.cutoff d (L.level r) j v := by
  have ha : (((((C₀).S.a (L.level r))^d : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_pos ((C₀).S.a_pos _) d).ne'
  simp only [RG17.atRef,lift,LinearEquiv.apply_symm_apply,map_smul,smul_smul,mul_inv_cancel₀ ha,one_smul]

theorem quotient (d : ℕ) (r : ℝ) (v : (C₀).label d) :
    S.project d (RG17.locatedRef L d r (lift R F L d r v)) =
    S.project d (L.charts d (L.level r) v) := by
  have ha : (((((C₀).S.a (L.level r))^d : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_pos ((C₀).S.a_pos _) d).ne'
  congr 1
  simp only [RG17.locatedRef,lift,LinearEquiv.apply_symm_apply,map_smul,smul_smul,mul_inv_cancel₀ ha,one_smul]

def pulled (d k : ℕ) (j : UVIndex) (v : (C₀).label d) :=
  atK C₀ F.room.cutoff d k j v

structure Receipt (d k : ℕ) (j : UVIndex) (v w : (C₀).label d) : Prop where
  left : (((C₀).factory d j.1 j.2).entries k (((C₀).factory d j.1 j.2).terminal.symm
    (pulled R F d k j v))).x = v
  right : (((C₀).factory d j.1 j.2).entries k (((C₀).factory d j.1 j.2).terminal.symm
    (pulled R F d k j w))).x = w
  field : ∀ g : ℝ,g≠0 → ∀ x y U,
    (C₀).O j.1 j.2 (pulled R F d k j v) x U * (C₀).O j.1 j.2 (pulled R F d k j w) y U =
    ((((C₀).S.a j.1:ℂ)^d)⁻¹)^2 *
      (WilsonFactoryBoxedFields.word R d j.1 j.2 (pulled R F d k j v) g x U *
       WilsonFactoryBoxedFields.word R d j.1 j.2 (pulled R F d k j w) g y U)

theorem deposit (d k : ℕ) (h : (C₀).ref d ≤ k) (j : UVIndex) (hj : k ≤ j.1)
    (v w : (C₀).label d) : Receipt R F d k j v w := by
  refine ⟨head R F d k h j hj v,head R F d k h j hj w,?_⟩
  intro g hg x y U
  rw [WilsonFactoryBoxedFields.field R d j.1 j.2 (pulled R F d k j v) hg,
    WilsonFactoryBoxedFields.field R d j.1 j.2 (pulled R F d k j w) hg,pow_two]
  exact mul_mul_mul_comm _ _ _ _

end YM.Integration.WilsonFactoryReportedChart
