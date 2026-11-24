import YM.Lattice.Support

/-!
# The inversion quotient regulator of §orbpt

All spacings are native in this file. The involution on *positive* edges reverses
transport, including on those incident to one of the singular sites. Use all edges of
the quotient multigraph. We don't turn it into a simple graph. Representatives can be
chosen especially simply by a Z/2 parity argument.
-/
set_option autoImplicit false

noncomputable section
namespace YM.XSpace
open Lattice Function Set

structure Period where
  side : Side
  even : 2 ∣ side.val
  large : 4 ≤ side.val

namespace Period

variable (R : Period)
abbrev Sites := Site R.side
abbrev Bonds := Edge R.Sites

/-- Base of the positive edge corresponding to the image (after reversing orientation). -/
def reflect (e : R.Bonds) : R.Bonds := (- e.1 - step e.2, e.2)

@[simp] lemma reflect_axis (e : R.Bonds) : (R.reflect e).2 = e.2 := rfl
@[simp] lemma reflect_dest (e : R.Bonds) : (R.reflect e).1 + step e.2 = -e.1 := sub_add_cancel ..
lemma reflect_base (e : R.Bonds) : (R.reflect e).1 = -(e.1 + step e.2) := by unfold reflect; dsimp; abel
@[simp] lemma reflect_invol (e : R.Bonds) : R.reflect (R.reflect e) = e := by
  refine Prod.ext ?_ rfl; dsimp [reflect]; abel

def parity : Per R.side →+* ZMod 2 := ZMod.castHom R.even (ZMod 2)

def Chosen (e : R.Bonds) : Prop := R.parity (e.1 e.2) = 0
instance : DecidablePred R.Chosen := fun e => by unfold Chosen; infer_instance

@[simp] lemma choice_reflect (e : R.Bonds) : R.Chosen (R.reflect e) ↔ ¬ R.Chosen e := by
  have h (z : ZMod 2) : z-1=0 ↔ z≠0 := by revert z; decide
  simp [Chosen, reflect, h]

lemma reflect_ne (e : R.Bonds) : R.reflect e ≠ e := fun he => by
  have hx:=R.choice_reflect e; rw [he] at hx; tauto

/-- Positive edge-orbit coordinates retaining endpoints as well as axis.
Gauge action uses endpoints in `Vertex`, not raw endpoints in `Sites`. -/
abbrev Link := {e : R.Bonds // R.Chosen e}

def rep (e : R.Bonds) : R.Link := if h : R.Chosen e then ⟨e,h⟩
    else ⟨R.reflect e,(R.choice_reflect e).mpr h⟩

@[simp] lemma rep_fixes (e : R.Link) : R.rep e.val = e := by simp [rep, e.property]
lemma rep_chosen (e : R.Bonds) (h : R.Chosen e) : (R.rep e).val=e := by simp [rep,h]
lemma rep_other (e : R.Bonds) (h : ¬ R.Chosen e) : (R.rep e).val=R.reflect e := by simp [rep,h]
@[simp] lemma rep_reflect (e : R.Bonds) : R.rep (R.reflect e)=R.rep e := by
  apply Subtype.ext; by_cases h : R.Chosen e <;> simp [rep, h]

lemma rep_eq_iff (e f : R.Bonds) : R.rep e = R.rep f ↔ f=e ∨ f=R.reflect e := by
  refine ⟨fun h=>?_,fun h=> ?_⟩
  · have he:=congr_arg Subtype.val h; by_cases hf:R.Chosen f <;> by_cases hh:R.Chosen e
    · left; rwa [eq_comm,R.rep_chosen f hf,R.rep_chosen e hh] at he
    · right; rwa [eq_comm,R.rep_other e hh,R.rep_chosen f hf] at he
    · right; rw [R.rep_chosen e hh, R.rep_other f hf] at he; rw [he,reflect_invol]
    left; rw [R.rep_other e hh, R.rep_other f hf] at he
    exact (show Function.Involutive R.reflect from R.reflect_invol).injective he.symm
  rcases h with h|h <;> simp [h]

def vertexSetoid : Setoid R.Sites where
  r x y:= y=x ∨ y= -x
  iseqv:= ⟨fun _=> .inl rfl,by
    intro x y h; rcases h with h|h <;> simp [h],by
    intro x y z h p; rcases h with h|h <;> rcases p with p|p <;> simp [h,p]⟩

/-- Vertex orbits including singleton orbits at singular sites. -/
def Vertex := Quotient R.vertexSetoid

def vertex (x : R.Sites) : R.Vertex := Quotient.mk R.vertexSetoid x

theorem vertex_surjective : Function.Surjective R.vertex := Quotient.mk_surjective
instance : Finite R.Vertex := .of_surjective _ R.vertex_surjective
instance : Fintype R.Vertex := Fintype.ofFinite _
instance : DecidableEq R.Vertex := Classical.typeDecidableEq _

theorem vertex_eq_iff (x y : R.Sites) : R.vertex x = R.vertex y ↔ y=x ∨ y= -x := @Quotient.eq' _ _ _ _
@[simp] lemma vertex_neg (x : R.Sites) : R.vertex (-x)=R.vertex x := ((R.vertex_eq_iff x (-x)).2 (.inr rfl)).symm

def src (e : R.Link) := R.vertex e.val.1
def dst (e : R.Link) := R.vertex (e.val.1+step e.val.2)

theorem rep_sites (e : R.Bonds) (h : R.Chosen e) : R.src (R.rep e)=R.vertex e.1 ∧
    R.dst (R.rep e)=R.vertex (e.1+step e.2) := by simp [src,dst,R.rep_chosen _ h]
theorem rep_sites' (e : R.Bonds) (h : ¬ R.Chosen e) : R.src (R.rep e)=R.vertex (e.1+step e.2) ∧
    R.dst (R.rep e)=R.vertex e.1 := by
  constructor
  · rw [src,R.rep_other _ h,reflect_base,vertex_neg]
  rw [dst,R.rep_other _ h,reflect_axis,reflect_dest,vertex_neg]

/-- Connects, forgetting orientation but keeping the edge. -/
def Joins (x y : R.Vertex) (e : R.Link) := R.src e = x ∧ R.dst e = y ∨ R.src e = y ∧ R.dst e=x
lemma flip {x y : R.Vertex} {e : R.Link} (h : R.Joins x y e) : R.Joins y x e := h.symm
lemma along (e : R.Bonds) : R.Joins (R.vertex e.1) (R.vertex (e.1+step e.2)) (R.rep e) := by
  by_cases h : R.Chosen e
  · exact .inl (R.rep_sites e h)
  exact .inr (R.rep_sites' e h)
lemma joins_step (x : R.Sites) (d : Step) : R.Joins (R.vertex x) (R.vertex (x+d.vec)) (R.rep (d.used x)) := by
  rcases d with ⟨i,b|b⟩
  · exact R.along (x,i)
  have h := R.flip (R.along (x-step i,i)); simpa [Step.used,Step.vec,sub_eq_add_neg] using h

inductive Path (p : Period) : p.Vertex → p.Vertex → ℕ → Prop where
  | nil (x) : p.Path x x 0
  | cons {x y z m} (e : p.Link) : p.Joins x y e → p.Path y z m → p.Path x z (m+1)

lemma path_of_walk (w : Walk) (x : R.Sites) : R.Path (R.vertex x) (R.vertex (stop x w)) w.length := by
  induction w generalizing x with
  | nil => exact .nil _
  | cons d w ih => exact .cons _ (R.joins_step x d) (ih (x+d.vec))

lemma exists_walk (x y : R.Sites) : ∃ w : Walk, stop x w = y := by
  let w := route (Lattice.lift x) (Lattice.lift y) 1
  exact ⟨w, calc
    _ = stop (wrap _ (Lattice.lift x)) w := by rw [wrap_lift]
    _ = _ := (wrap_stop_cover _ _).symm.trans (by unfold w; rw [route_end,wrap_lift])⟩

theorem connected (x y : R.Vertex) : ∃ m, R.Path x y m := by
  obtain ⟨x,rfl⟩:=R.vertex_surjective x; obtain ⟨y,rfl⟩:=R.vertex_surjective y
  obtain ⟨w,h⟩:=R.exists_walk x y; rw [← h]
  exact ⟨w.length,R.path_of_walk w x⟩

end Period
end YM.XSpace
