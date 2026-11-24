import YM.Wilson.Law
import YM.Lattice.Support
import YM.Gauge.Colors

/-!
# Inversion quotient regulator

The cover is the (finite) full periodic lattice. `Regulator.Vertex` is one site
per inversion orbit, including self-orbits. `Regulator.Link` is one unoriented
link per inversion orbit, carrying one Haar link. Incidences on the quotient
(multigraph convention) keep separate edges, even if the resulting endpoints
agree with those of another edge.

The action is half the full Wilson action on the cover restricted to the
equivariant configurations; this is for use as a *perturbative regulator*,
not a change of the Wilson law of the construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Lattice Wilson MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

-- helper: arbitrary consistent orientation/choice (need not respect lattice tensor group)
private def pairs {α : Type*} {f : α → α} (hf : Involutive f) : Setoid α where
  r x y := x=y ∨ f x=y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun {x y} h => by
      rcases h with rfl|rfl
      · left; rfl
      right; exact hf _
    trans := fun {x y z} h g => by
      rcases h with rfl|rfl
      · exact g
      rcases g with rfl|rfl
      · right; rfl
      left; exact (hf _).symm }

private lemma orbit_choice {α : Type*} {f : α → α} (hf : Involutive f) :
    ∃ r : α → α, ∀ x, (r x=x ∨ r x=f x) ∧ r (f x) = r x := by
  let q := Quotient.mk (pairs hf)
  let r (x) := @Quotient.out _ (pairs hf) (q x)
  refine ⟨r,fun x => ⟨?_,?_⟩⟩
  · have h : q x = q (r x) := (@Quotient.out_eq _ (pairs hf) _).symm
    rcases (show x=r x ∨ f x=r x from Quotient.exact h) with h|h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  exact congrArg (@Quotient.out _ (pairs hf)) (show q (f x) = q x from (Quotient.sound (show x=f x ∨ f x=f x from Or.inr rfl)).symm)

structure Regulator where
  side : Side
  even : 2 ∣ side.val
  size : 4 ≤ side.val

namespace Regulator
variable (R : Regulator)
abbrev LSite := Site R.side
abbrev LEdge := Edge R.LSite

def antipode (e : R.LEdge) : R.LEdge := (-(e.1+step e.2), e.2)
@[simp] theorem antipode_invol (e : R.LEdge) : R.antipode (R.antipode e) = e := by
  unfold antipode; simp

theorem antipode_free (e : R.LEdge) : R.antipode e ≠ e := by
  intro h
  let q := ZMod.castHom R.even (ZMod 2)
  have he := congrArg (fun v : R.LEdge => q (v.1 e.2)) h
  simp only [antipode, Pi.neg_apply, Pi.add_apply, step_apply, ite_true, map_neg, map_add, map_one] at he
  revert he
  generalize q (e.1 e.2) = a
  revert a
  decide

def siteRep := Classical.choose (orbit_choice (α:=R.LSite) (f:=Neg.neg) neg_neg)
def edgeRep := Classical.choose (orbit_choice (R.antipode_invol))
theorem siteRep_cases (x : R.LSite) : R.siteRep x = x ∨ R.siteRep x = -x :=
  (Classical.choose_spec (orbit_choice (f:=Neg.neg) neg_neg) x).1
@[simp] theorem siteRep_neg (x : R.LSite) : R.siteRep (-x) = R.siteRep x :=
  (Classical.choose_spec (orbit_choice (f:=Neg.neg) neg_neg) x).2
theorem edgeRep_cases (e : R.LEdge) : R.edgeRep e = e ∨ R.edgeRep e = R.antipode e :=
  (Classical.choose_spec (orbit_choice R.antipode_invol) e).1
@[simp] theorem edgeRep_anti (e : R.LEdge) : R.edgeRep (R.antipode e) = R.edgeRep e :=
  (Classical.choose_spec (orbit_choice R.antipode_invol) e).2
@[simp] theorem siteRep_rep (x : R.LSite) : R.siteRep (R.siteRep x) = R.siteRep x := by
  rcases R.siteRep_cases x with h|h
  · nth_rw 1 [h]
  nth_rw 1 [h]
  exact R.siteRep_neg x
@[simp] theorem edgeRep_rep (x : R.LEdge) : R.edgeRep (R.edgeRep x) = R.edgeRep x := by
  rcases R.edgeRep_cases x with h|h
  · nth_rw 1 [h]
  nth_rw 1 [h]; exact R.edgeRep_anti x

abbrev Vertex := {x : R.LSite // R.siteRep x = x}
abbrev Link := {e : R.LEdge // R.edgeRep e = e}

def vertex (x : R.LSite) : R.Vertex := ⟨_,R.siteRep_rep x⟩
def link (e : R.LEdge) : R.Link := ⟨_,R.edgeRep_rep e⟩
@[simp] theorem vertex_rep (v : R.Vertex) : R.vertex v.val = v := Subtype.ext v.property
@[simp] theorem link_rep (l : R.Link) : R.link l.val = l := Subtype.ext l.property
@[simp] theorem vertex_neg (x : R.LSite) : R.vertex (-x) = R.vertex x := Subtype.ext (R.siteRep_neg x)
@[simp] theorem link_anti (e : R.LEdge) : R.link (R.antipode e) = R.link e := Subtype.ext (R.edgeRep_anti e)

def src (l : R.Link) := R.vertex l.val.1
def dst (l : R.Link) := R.vertex (l.val.1 + step l.val.2)

def root := R.vertex 0

def Joins (l : R.Link) (a b : R.Vertex) :=
  (R.src l=a ∧ R.dst l=b) ∨ (R.src l=b ∧ R.dst l=a)

lemma joins_of_rep (e : R.LEdge) : R.Joins (R.link e) (R.vertex e.1) (R.vertex (e.1 + step e.2)) := by
  rcases R.edgeRep_cases e with h|h
  · left; simp [src,dst,link,h]
  right; simp only [src,dst,link,h,antipode,R.vertex_neg]
  simp

lemma Joins.symm {l a b} (h : R.Joins l a b) : R.Joins l b a := Or.symm h

variable {G : Gauge}

abbrev Configuration (R : Regulator) (G : Gauge) := R.Link → G.El

def Lift (U : R.Configuration G) (e : R.LEdge) := if R.edgeRep e=e then U (R.link e) else (U (R.link e))⁻¹
@[simp] theorem Lift_link (U : R.Configuration G) (l : R.Link) : R.Lift U l.val= U l := by
  simp [Lift,l.property]
theorem Lift_anti (U : R.Configuration G) (e : R.LEdge) : R.Lift U (R.antipode e)= (R.Lift U e)⁻¹ := by
  rcases R.edgeRep_cases e with h|h
  · simp [Lift,h,(R.antipode_free e).symm]
  simp [Lift,h,R.antipode_free e]

def Vague (g : R.Vertex → G.El) (U : R.Configuration G) (l : R.Link) :=
  g (R.src l) * U l * (g (R.dst l))⁻¹
@[simp] theorem Lift_gauge (g : R.Vertex → G.El) (U : R.Configuration G) :
    R.Lift (R.Vague g U) = Lattice.gauge (g ∘ R.vertex) (R.Lift U) := by
  ext1 e
  rcases R.edgeRep_cases e with h|h
  · simp [Lift,Vague,link, h,Lattice.gauge,src,dst]
  · simp only [Lift,h,if_neg (R.antipode_free _),Lattice.gauge,Vague,src,dst,
        mul_inv_rev, inv_inv, link,Function.comp_apply]
    simp only [antipode,R.vertex_neg]
    simp [mul_assoc]

def orbitEnergy (U : R.Configuration G) := energy (R.Lift U) / 2
@[simp] theorem orbitEnergy_gauge (g : R.Vertex → G.El) (U : R.Configuration G) :
    R.orbitEnergy (R.Vague g U)= R.orbitEnergy U := by
  simp only [orbitEnergy,R.Lift_gauge, energy_gauge]
@[fun_prop] theorem Lift_cont : Continuous (R.Lift (G:=G)) := by
  refine continuous_pi fun e => ?_
  simp only [Lift]
  split <;> fun_prop
@[fun_prop] theorem orbitEnergy_cont : Continuous (R.orbitEnergy (G:=G)) := by unfold orbitEnergy; fun_prop

def orbitPrior (G : Gauge) := Measure.pi (fun _ : R.Link => G.probHaar)
instance : IsProbabilityMeasure (R.orbitPrior G) := by unfold orbitPrior; infer_instance

/-! Linearized links -/

abbrev Potential (R : Regulator) (G : Gauge) := R.Link → G.Color

def liftA (G : Gauge) : R.Potential G →ₗ[ℝ] (R.LEdge → G.Color) where
  toFun A e := if R.edgeRep e=e then A (R.link e) else - A (R.link e)
  map_add' A B := by funext e; simp only [Pi.add_apply]; split <;> simp_all [add_comm]
  map_smul' c A := by funext e; simp

@[simp] theorem liftA_link (A : R.Potential G) (l : R.Link) : R.liftA G A l.val=A l := by
  simp [liftA,l.property]

theorem liftA_anti (A : R.Potential G) (e : R.LEdge) : R.liftA G A (R.antipode e)= - R.liftA G A e := by
  rcases R.edgeRep_cases e with h|h
  · simp [liftA,h,(R.antipode_free e).symm]
  simp [liftA,h,R.antipode_free e]

-- alignment with the physical color normalization of the baseline
lemma lieExp_minus (x : G.Color) : G.lieExp (-x) = (G.lieExp x)⁻¹ := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply eq_inv_of_mul_eq_one_left
  apply G.mat_injective
  simp only [G.mat_mul,G.mat_one,G.mat_lieExp,map_neg]
  have he : NormedSpace.exp (-G.colorMat x + G.colorMat x) = NormedSpace.exp (-(G.colorMat x)) * NormedSpace.exp (G.colorMat x) := NormedSpace.exp_add_of_commute ((Commute.refl (G.colorMat x)).neg_left)
  rw [← he]; simp

theorem Lift_exp (A : R.Potential G) (g : ℝ) :
    R.Lift (fun l => G.lieExp (g • A l)) = fun e => G.lieExp (g • R.liftA G A e) := by
  ext1 e
  by_cases h : R.edgeRep e=e <;> simp [Lift,h,liftA,lieExp_minus]

end Regulator
end YM.XSpace
