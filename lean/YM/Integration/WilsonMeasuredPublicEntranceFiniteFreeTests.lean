import YM.Integration.WilsonPhysicalPositionBornCandidates
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Finite actual smooth separated position tests for the complete multiplicative free
moment stabilizer on the original finite physical horizon. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 12000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFiniteFreeTests
open Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize MvPolynomial
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}{I:Type*}[Fintype I]

private theorem finite_equations {A T:Type*}[Fintype A](p:T→MvPolynomial A ℂ):
    ∃s:Finset T,∀z:A→ℂ,(∀t∈s,eval z (p t)=0)↔∀t,eval z (p t)=0:=by
  classical
  let R:=MvPolynomial A ℂ
  obtain ⟨small,select,all⟩:∃s:Finset R,↑s⊆range p ∧
      Submodule.span R (range p)=Submodule.span R (s:Set R):=
    (Submodule.fg_span_iff_fg_span_finset_subset (range p)).mp (IsNoetherian.noetherian _)
  choose source original using fun a:small=>select a.property
  refine ⟨Finset.univ.image source,fun z=>⟨?_,fun h t _=>h t⟩⟩
  intro test t
  have contained:Ideal.span (range p)≤RingHom.ker (eval z):=by
    change Submodule.span R (range p)≤_
    rw [all]
    apply Submodule.span_le.mpr
    intro a ha
    have ok:=test (source ⟨a,ha⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [original ⟨a,ha⟩] at ok
    exact ok
  exact contained (Ideal.subset_span (mem_range_self t))

structure Hearing (I:Type*) where
  arity:ℕ
  profile:Test arity
  inputs:Fin arity→I

def heard (e:Module.Basis I ℂ (Sec G d))(T:FieldEnd G d)(h:Hearing I):ℂ:=
  let L:=reference G d h.arity h.profile
  L (fun i=>T (e (h.inputs i)))-L (fun i=>e (h.inputs i))

private def equation (e:Module.Basis I ℂ (Sec G d))(h:Hearing I):MvPolynomial (I×I) ℂ:=
  let L:=reference G d h.arity h.profile
  (∑j:Fin h.arity→I,C (L (fun i=>e (j i)))*∏i:Fin h.arity,X (j i,h.inputs i))-
    C (L (fun i=>e (h.inputs i)))

private theorem evaluated (e:Module.Basis I ℂ (Sec G d))(T:FieldEnd G d)(h:Hearing I):
    eval (fun p:I×I=>e.coord p.1 (T (e p.2))) (equation e h)=heard e T h:=by
  let L:=reference G d h.arity h.profile
  let a(i:Fin h.arity):I→Sec G d:=fun j=>e.coord j (T (e (h.inputs i))) • e j
  have paid(i:Fin h.arity): T (e (h.inputs i))=∑j,a i j:=(e.sum_repr _).symm
  unfold heard equation
  simp only [map_sub,map_sum,map_mul,map_prod,eval_C,eval_X]
  congr 1
  change _=L (fun i=>T (e (h.inputs i)))
  rw [show (fun i=>T (e (h.inputs i)))=(fun i=>∑j,a i j) from funext paid]
  rw [L.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold a
  rw [L.map_smul_univ]
  simp only [smul_eq_mul]
  ring

theorem original (e:Module.Basis I ℂ (Sec G d)):
    ∃s:Finset (Hearing I),∀T:FieldEnd G d,
      (∀h∈s,heard e T h=0)↔recruit T (reference G d)=reference G d:=by
  obtain ⟨s,done⟩:=finite_equations (equation e)
  refine ⟨s,fun T=>?_⟩
  have all:=done (fun p:I×I=>e.coord p.1 (T (e p.2)))
  simp_rw [evaluated] at all
  rw [all]
  constructor
  · intro full
    funext n
    apply LinearMap.ext
    intro t
    apply Module.Basis.ext_multilinear (fun _:Fin n=>e)
    intro v
    exact sub_eq_zero.mp (full ⟨n,t,v⟩)
  intro agreed h
  exact sub_eq_zero.mpr (congrArg (fun P:Prediction G d=>P h.arity h.profile (fun i=>e (h.inputs i))) agreed)

theorem recorded (C:Family G)(d:ℕ):
    let e:=(Extra.FD.recorded C.labels d).b.map (fields C.labels d)
    ∃s:Finset (Hearing (Fin ((Extra.FD.recorded C.labels d).m+1))),∃n:ℕ,
      (∀h∈s,h.arity≤n) ∧ ∀T:FieldEnd G d,
      (∀h∈s,heard e T h=0)↔recruit T (reference G d)=reference G d:=by
  let e:=(Extra.FD.recorded C.labels d).b.map (fields C.labels d)
  obtain ⟨s,hs⟩:=original e
  exact ⟨s,s.sup Hearing.arity,fun _ h=>Finset.le_sup h,hs⟩
end YM.Integration.WilsonMeasuredPublicEntranceFiniteFreeTests

