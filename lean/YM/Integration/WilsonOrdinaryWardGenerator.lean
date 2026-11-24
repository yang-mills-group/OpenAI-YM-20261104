import YM.Integration.WilsonOrdinaryWardSpace
import YM.Integration.WilsonFactoryOwnHeight

/-! The admissible real parameter space actually contains identity on every
true positive top stratum, including every named independent MS glyph on
that stratum. This excludes a vacuous restricted normalization. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryWardGenerator
open Function Matrix Filter Set Finset Pert Pert.Position MS MS.Theater MS.Menus MS.Land MS.Local.Physical
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Table Spec Climb PhysMS Maxwell Trace.Pilot
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
open WilsonOrdinaryWardSpace
variable {G : Gauge} (C : Family G) (B : Deck G)
local notation "b₀" => WilsonMacroscopicRichFree.basis C B

theorem located (h : ℕ) (a : Glyph B h) :
    act C B h (mask B h) (b₀ h a) = if a.size=h then b₀ h a else 0 := by
  let e := (b₀ h).equivFun
  have name : e (b₀ h a)=Pi.single a 1 := by
    ext i
    simp [e,Pi.single_apply,eq_comm]
  apply e.injective
  rw [act,show (b₀ h).equivFun.symm=e.symm from rfl,LinearEquiv.apply_symm_apply,name]
  by_cases size : a.size=h
  · rw [if_pos size,name];ext i;by_cases eq : a=i
    · subst i;simp [mask,Matrix.vecMul,dotProduct,Matrix.diagonal_apply,Pi.single_apply,size]
    · simp [mask,Matrix.vecMul,dotProduct,Matrix.diagonal_apply,Pi.single_apply,eq,eq_comm]
  · rw [if_neg size,map_zero];ext i
    simp [mask,Matrix.vecMul,dotProduct,Matrix.diagonal_apply,Pi.single_apply,eq_comm]
    rintro hs rfl;exact size hs.symm

theorem below (d : ℕ) (a : Glyph B (d+1)) (low : a.size≠d+1) :
    ∃ v : (Bel C.book).Field d,(Free.scheme C.labels).rise (Nat.le_succ d) v=b₀ (d+1) a := by
  have bound := Nat.le_of_lt_succ a.1.isLt
  have truth : a.1.val≤d := by change a.1.val≠d+1 at low;omega
  let x := WilsonFactoryOwnHeight.ground (C:=C) B a
  refine ⟨(Free.scheme C.labels).rise truth x,?_⟩
  rw [(Free.scheme C.labels).transit (table_sym C.labels) (Free.scheme_filters C.labels)]
  exact (WilsonFactoryOwnHeight.input (C:=C) B a).trans (WilsonOrdinaryPositionGrades.free_glyph (C:=C) B (d+1) a).symm

def linear (d : ℕ) (A : Matrix (Glyph B d) (Glyph B d) ℂ) :
    (Bel C.book).Field d →ₗ[ℂ] (Bel C.book).Field d :=
  (b₀ d).equivFun.symm.toLinearMap.comp (A.vecMulLinear.comp (b₀ d).equivFun.toLinearMap)

theorem window (d : ℕ) (v : (Bel C.book).Field (d+1)) :
    act C B (d+1) (mask B (d+1)) v = v -
      (Free.scheme C.labels).rise (Nat.le_succ d) (PhysMS.Frame.peelDown C d v) := by
  let Y := linear C B (d+1) (mask B (d+1))
  let T := LinearMap.id - ((Free.scheme C.labels).rise (Nat.le_succ d)).comp (PhysMS.Frame.peelDown C d)
  have maps : Y=T := by
    apply (b₀ (d+1)).ext;intro a
    change act C B (d+1) (mask B (d+1)) (b₀ (d+1) a) =
      (b₀ (d+1) a) - (Free.scheme C.labels).rise (Nat.le_succ d) (PhysMS.Frame.peelDown C d (b₀ (d+1) a))
    rw [located]
    by_cases own : a.size=d+1
    · rw [if_pos own,PhysMS.Frame.section_same d _ (WilsonOrdinaryPositionGrades.named B (d+1) a own),map_zero,sub_zero]
    · obtain ⟨u,hu⟩ := below C B d a own
      rw [if_neg own,←hu,PhysMS.Frame.section_up,sub_self]
  exact LinearMap.congr_fun maps v

theorem honest (hG : G.Simple) (H : (Bel C.book).Hierarchy) (d : ℕ) :
    mask B (d+1)∈directions C B (d+1) H := by
  have grade : mask B (d+1)*mask B (d+1)=mask B (d+1) := by
    ext a b;rw [WilsonOrdinaryWardSpace.row]
    by_cases same : a.size=d+1
    · rw [if_pos same]
    · rw [if_neg same];simp [mask,Matrix.diagonal_apply,same]
  refine ⟨grade,?_,?_,?_⟩
  · rw [window,←(Free.scheme C.labels).fixs (Free.scheme_filters C.labels) H.laws (Nat.le_succ d),
      PhysMS.Frame.section_up,sub_self]
  · intro v
    rw [window,window,PhysMS.Frame.section_real H,map_sub,(Free.phase_orientation C.labels).realInc]
  · intro s v
    rw [window,window,PhysMS.Frame.section_rotation hG,map_sub,(baseRights (C:=C) (H:=H) hG).filtered]

/-- Each named own-height positive label is a nonzero priced parameter of
the genuine physical admissible normalization. -/
theorem present (hG : G.Simple) (H : (Bel C.book).Hierarchy) (d : ℕ) (a : Glyph B (d+1)) (h : a.size=d+1) :
    ∃ Δ : directions C B (d+1) H,Δ.val a a=1 ∧ act C B (d+1) Δ.val (b₀ (d+1) a)=b₀ (d+1) a := by
  refine ⟨⟨mask B (d+1),honest C B hG H d⟩,?_,?_⟩
  · simp [mask,h]
  · rw [located,if_pos h]

end YM.Integration.WilsonOrdinaryWardGenerator
end

