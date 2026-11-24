import YM.Integration.WilsonOrdinaryPositionGrades

/-! The actual real, O(4)-equivariant, vacuum-preserving corrections to the
Maxwell field, measured only on incoming fields of the honest native grade.
This subspace is fixed before either physical or perturbative Gram matrix. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryWardSpace
open Function Filter Matrix Pert MS MS.Menus MS.Land MS.Local.Physical MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Table Spec Climb PhysMS Maxwell Trace.Pilot
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) (B : Deck G) (d : ℕ)
local notation "Iₕ" => Glyph B d

def mask : Matrix Iₕ Iₕ ℂ := Matrix.diagonal (fun i=>if i.size=d then 1 else 0)

theorem row (A : Matrix Iₕ Iₕ ℂ) (a b : Iₕ) :
    (mask B d*A) a b = if a.size=d then A a b else 0 := by
  rw [mask,Matrix.diagonal_mul];split <;> simp_all

def act (A : Matrix Iₕ Iₕ ℂ) (v : (Bel C.book).Field d) : (Bel C.book).Field d :=
  (WilsonMacroscopicRichFree.basis C B d).equivFun.symm
    (A.vecMul ((WilsonMacroscopicRichFree.basis C B d).equivFun v))

theorem identity (v : (Bel C.book).Field d) : act C B d 1 v=v := by
  rw [act,Matrix.vecMul_one,LinearEquiv.symm_apply_apply]

theorem cleared (v : (Bel C.book).Field d) : act C B d 0 v=0 := by
  rw [act,Matrix.vecMul_zero,map_zero]

theorem add (A Z : Matrix Iₕ Iₕ ℂ) (v : (Bel C.book).Field d) :
    act C B d (A+Z) v=act C B d A v + act C B d Z v := by
  simp only [act,Matrix.vecMul_add,map_add]

theorem scale (t : ℝ) (A : Matrix Iₕ Iₕ ℂ) (v : (Bel C.book).Field d) :
    act C B d (t • A) v=t • act C B d A v := by
  simp only [act,RCLike.real_smul_eq_coe_smul (K:=ℂ),Matrix.vecMul_smul,map_smul]

variable (H : (Bel C.book).Hierarchy)

def directions : Submodule ℝ (Matrix Iₕ Iₕ ℂ) where
  carrier := {A | mask B d*A=A ∧ act C B d A ((Bel C.book).unit d)=0 ∧
    (∀ v,act C B d A ((Bel C.book).conj H.spin d v) = (Bel C.book).conj H.spin d (act C B d A v)) ∧
    ∀ s v,act C B d A ((turns C).act d s v)=(turns C).act d s (act C B d A v)}
  zero_mem' := by
    exact ⟨mul_zero _,cleared ..,fun v=>by rw [cleared,cleared,map_zero],fun s v=>by rw [cleared,cleared,map_zero]⟩
  add_mem' := by
    intro A Z a z
    exact ⟨by rw [mul_add,a.1,z.1],by rw [add,a.2.1,z.2.1,add_zero],
      fun v=>by rw [add,add,map_add,a.2.2.1,z.2.2.1],
      fun s v=>by rw [add,add,map_add,a.2.2.2,z.2.2.2]⟩
  smul_mem' := by
    intro t A a
    refine ⟨by rw [mul_smul_comm,a.1],by rw [scale,a.2.1,smul_zero],?_,?_⟩
    · intro v
      rw [scale,scale,a.2.2.1,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,RCLike.conj_ofReal]
    · intro s v
      rw [scale,scale,a.2.2.2,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]

variable {f : Extraction.Order} {S : Table C.book} (F : Final C f S)

theorem physical (J Y : PhysMS.tower S) (before : PhysMS.Frame.obedient F H J d)
    (Δ : directions C B d H) (actual : ∀ v,Y d v=J d (act C B d (1+Δ.val) v)) :
    PhysMS.Frame.obedient F H Y d := by
  have acts (v) : Y d v=J d (v+act C B d Δ.val v) := by rw [actual,add,identity]
  refine ⟨?_,?_,?_⟩
  · intro v
    rw [acts,Δ.property.2.2.1,←map_add,before.real,acts]
  · rw [acts,Δ.property.2.1,add_zero,before.unit]
  · intro s v
    rw [acts,Δ.property.2.2.2,←map_add,before.axis,acts]

end YM.Integration.WilsonOrdinaryWardSpace
end

