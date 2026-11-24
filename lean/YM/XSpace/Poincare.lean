import YM.XSpace.TreeGauge

/-! # Curl and the absence of harmonic one-forms in the orbifold perturbative regulator -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Lattice Wilson MeasureTheory
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

section Lattice
variable {n : Side}
variable {V : Type*} [AddCommGroup V]

def curl (A : Edge (Site n) → V) (x : Site n) (a b : Axis) :=
  A (x,a) + A (x+step a,b) - A (x+step b,a) - A (x,b)
def field (A : Edge (Site n) → V) (p : Face (Per n)) := curl A p.1 p.2.val.1 p.2.val.2

theorem curl_sub (A B : Edge (Site n) → V) (x a b) : curl (A-B) x a b = curl A x a b - curl B x a b := by
  simp only [curl, Pi.sub_apply]; abel

def grad (w : Site n → V) (e : Edge (Site n)) := w (e.1+step e.2)-w e.1

theorem curl_grad (w : Site n → V) (x a b) : curl (grad w) x a b=0 := by
  unfold curl grad; rw [add_right_comm x]; abel

theorem curl_swap (A : Edge (Site n) → V) (x a b) : curl A x a b = -curl A x b a := by unfold curl; abel

theorem curl_zero_of_field_zero (A : Edge (Site n) → V) (h : field A = 0) (x a b) : curl A x a b = 0 := by
  rcases lt_trichotomy a b with ha|ha|ha
  · exact congr_fun h (x,⟨(a,b),ha⟩)
  · rw [ha]; unfold curl; abel
  rw [curl_swap, show curl A x b a=0 from congr_fun h (x,⟨(b,a),ha⟩),neg_zero]

def increment (A : Edge (Site n) → V) (x : Site n) (d : Step) := if d.neg then -A (d.used x) else A (d.used x)
def transport (A : Edge (Site n) → V) (x : Site n) : Walk → V
| []=>0
| d::w=> increment A x d + transport A (x+d.vec) w

lemma transport_shift (A : Edge (Site n) → V) (ha : field A=0) (x : Site n) (w : Walk) (a : Axis) :
    transport A (x+step a) w - transport A x w = A (stop x w,a)-A (x,a) := by
  induction w generalizing x with
  | nil => simp [transport,stop]
  | cons d w ih =>
    rw [transport,transport, stop, add_right_comm x (step a), add_sub_add_comm, ih]
    suffices hx : increment A (x+step a) d - increment A x d = A (x+d.vec,a)-A (x,a) by rw [hx]; abel
    rcases d with ⟨b,p|p⟩
    · change A (x+step a,b) - A (x,b) = A (x+step b,a)-A (x,a)
      rw [← sub_eq_zero]
      refine Eq.trans ?_ (curl_zero_of_field_zero A ha x a b); unfold curl; abel
    · change -A (x+step a-step b,b) - -A (x-step b,b) = A (x + -step b,a)-_
      rw [← sub_eq_add_neg,add_sub_right_comm, ← sub_eq_zero]
      refine Eq.trans ?_ (neg_eq_zero.mpr (curl_zero_of_field_zero A ha (x-step b) a b)); unfold curl
      rw [sub_add_cancel]; abel

lemma stop_across (x y : Site n) (w : Walk) : stop (y+x) w = y+stop x w := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [stop,stop,add_assoc,ih]

def wander (x y : Site n) := route (lift x) (lift y) 1
@[simp] lemma wander_end (x y : Site n) : stop x (wander x y) = y := calc
  _ = stop (wrap n (lift x)) (wander x y) := by rw [wrap_lift]
  _ = _ := (wrap_stop_cover ..).symm
  _ = _ := by unfold wander; rw [route_end,wrap_lift]

lemma grad_zero {u : Site n → V} (hg : grad u=0) (x y : Site n) : u x=u y := by
  have he (x : Site n) (w : Walk) : u x=u (stop x w) := by
    induction w generalizing x with
    | nil=> rfl
    | cons d w ih=>
      rw [stop,← ih]; rcases d with ⟨a,b|b⟩
      · exact (sub_eq_zero.mp (show u (x+step a)-u x=0 from congr_fun hg (x,a))).symm
      · have h := sub_eq_zero.mp (show u (x-step a+step a)-u (x-step a)=0 from congr_fun hg (x-step a,a))
        rw [sub_add_cancel] at h; rwa [Step.vec,if_pos rfl,← sub_eq_add_neg]
  simpa using he x (wander x y)

variable [Module ℝ V]

def primitive (A : Edge (Site n) → V) (x : Site n) :=
  -(Fintype.card (Site n) : ℝ)⁻¹ • ∑ y : Site n, transport A x (wander 0 y)

lemma grad_of_mean (A : Edge (Site n) → V) (ha : field A=0) (hm : ∀ i : Axis, (∑ x : Site n,A (x,i))=0) :
    grad (primitive A)=A := by
  funext (x,a)
  unfold grad primitive
  rw [← smul_sub,← Finset.sum_sub_distrib]; simp_rw [transport_shift A ha]
  have he (y : Site n) : stop x (wander (0:Site n) y)=x+y := by
    simpa using stop_across 0 x (wander (0:Site n) y)
  simp_rw [he]; rw [Finset.sum_sub_distrib,
    show (∑ y : Site n, A (x+y,a))=_ from Equiv.sum_comp (Equiv.addLeft x) (fun y => A (y,a)), hm]
  simp [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
end Lattice

namespace Regulator
variable {R : Regulator} {G : Gauge}
lemma mean_zero (A : R.Potential G) (i : Axis) : ∑ x : R.LSite, R.liftA G A (x,i)=0 := by
  let e := (Equiv.addRight (step i : R.LSite)).trans (Equiv.neg _)
  let v (x : R.LSite) := R.liftA G A (x,i)
  have he (x) : v (e x)= -v x := R.liftA_anti A (x,i)
  have hh:= Equiv.sum_comp e v; rw [show (∑ x, v (e x))= -(∑ x, v x) by simp only [he, Finset.sum_neg_distrib]] at hh
  have hl : (2:ℝ) • (∑ x,v x)=0 := by rw [two_smul, ← hh]; nth_rw 2 [hh]; simp
  exact (smul_eq_zero.mp hl).resolve_left (by norm_num)

theorem exact_gradient (A : R.Potential G) (ha : field (R.liftA G A)=0) :
    ∃ v : R.Vertex → G.Color, R.liftA G A = grad (v ∘ R.vertex) := by
  let u := primitive (R.liftA G A)
  have hu : grad u=R.liftA G A := grad_of_mean _ ha (mean_zero A)
  have hv (x : R.LSite) : u x=u (-x) := by
    let w (x) := u (-x) - u x
    have he : grad w=0 := by
      funext (x,i)
      have hx := R.liftA_anti A (x,i); rw [← hu] at hx
      change u (-(x+step i)+step i) - u (-(x+step i)) = -(u (x+step i)-u x) at hx
      rw [show -(x+step i)+step i = -x by abel] at hx
      change w (x+step i)-w x=0
      unfold w; calc
        _ = -(u (-x)-u (-(x+step i))) - (u (x+step i) - u x) := by abel
        _ = 0 := by rw [hx]; simp
    exact Eq.symm (sub_eq_zero.mp (show w x=0 by rw [grad_zero he x 0]; simp [w]))
  refine ⟨fun v=>u v.val,?_⟩; rw [← hu]; apply congr_arg grad; funext x
  change u x=u (R.siteRep x); rcases R.siteRep_cases x with h|h <;> rw [h]; exact hv x
namespace Tree
variable (T : R.Tree)

abbrev Array (T : R.Tree) (G : Gauge) := T.Mobile → G.Color

def injection (G : Gauge) : T.Array G →ₗ[ℝ] R.Potential G where
  toFun A l := if h : l ∈ T.ties then 0 else A ⟨l,h⟩
  map_add' A B := by funext l; simp only [Pi.add_apply]; split <;> simp_all
  map_smul' c A := by funext l; simp only [RingHom.id_apply,Pi.smul_apply]; split <;> simp_all

@[simp] lemma injection_tie (A : T.Array G) (x : R.Nonroot) : T.injection G A (T.edge x)=0 := by
  simp [injection,show T.edge x ∈ T.ties from (T.twig x).property]
@[simp] lemma injection_mobile (A : T.Array G) (l : T.Mobile) : T.injection G A l.val=A l := by
  simp [injection,l.property]

def periodic (G : Gauge) : T.Array G →ₗ[ℝ] (R.LEdge → G.Color) := (R.liftA G).comp (T.injection G)

theorem flat_tree (A : T.Array G) (ha : field (T.periodic G A)=0) : A=0 := by
  obtain ⟨v,hv⟩ := R.exact_gradient (T.injection G A) ha
  have he (l : R.Link) : T.injection G A l = v (R.dst l) - v (R.src l) := by
    rw [← R.liftA_link (T.injection G A) l,hv]; rfl
  have hm (k : ℕ) (w : R.Vertex) (hh : T.depth w=k) : v w=v R.root := by
    induction k using Nat.strong_induction_on generalizing w with
    | h k ih =>
      by_cases h : w= R.root
      · rw [h]
      let a : R.Nonroot := ⟨w,h⟩
      have hx := T.lower a
      suffices v w=v (T.parent a) from this.trans (ih _ (show _<k from hh ▸ hx) _ rfl)
      have hi : v (R.dst (T.edge a)) = v (R.src (T.edge a)) := sub_eq_zero.mp (by rw [← he, injection_tie])
      rcases T.joins a with h|h <;> rw [h.1,h.2] at hi
      · exact hi
      exact hi.symm
  funext l
  change A l=0
  rw [← injection_mobile T A l, he, hm _ _ rfl, hm _ (R.src l.val) rfl, sub_self]
end Tree
end Regulator
end YM.XSpace
