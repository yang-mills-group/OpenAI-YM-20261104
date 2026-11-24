import YangMills.WilsonProof.NativeSupport.HierarchySpec

import YangMills.LatticeFields
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Adjoints and stencils in the graded finite-volume fields. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.Wilson

open Filter

open scoped BigOperators Topology

namespace WilsonData

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}

private theorem semilinear_on_basis {w : ℕ} (f h : RawSpace w →ₗ[ℂ] ℂ)
    (s : RawSpace w →ₛₗ[starRingEnd ℂ] RawSpace w)
    (hb : ∀ i, f (s ((Pi.basisFun ℂ (Fin w)) i)) = star (h ((Pi.basisFun ℂ (Fin w)) i))) :
    ∀ v, f (s v) = star (h v) := by
  have eqn : f.comp s = (starLinearEquiv ℂ (A := ℂ)).toLinearMap.comp h :=
    (Pi.basisFun ℂ (Fin w)).ext hb
  exact fun v => LinearMap.congr_fun eqn v

theorem gradeAdjoints (D : WilsonData B C) (d : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p (v : RawSpace (D.raw.width d)) x U,
      C.insertion N p (D.conjugate (D.raw.token ⟨d,v⟩)) x U =
        star (C.insertion N p (D.raw.token ⟨d,v⟩) x U) ∧
      C.insertion N p (D.starToken (D.raw.token ⟨d,v⟩)) (timeMirror x) U =
        star (C.insertion N p (D.raw.token ⟨d,v⟩) x (timeMirrorLinks U)) := by
  let b := Pi.basisFun ℂ (Fin (D.raw.width d))
  have tails := eventually_all.mpr (fun i : Fin (D.raw.width d) =>
    (D.reality (D.raw.token ⟨d,b i⟩)).and (D.reflection (D.raw.token ⟨d,b i⟩)))
  filter_upwards [tails] with N hN
  intro p v x U
  let read y W := (D.raw.linear N p d y W).mk' _
  constructor
  · rw [← D.raw.tokenBar]
    exact semilinear_on_basis (read x U) (read x U) (D.raw.bar d)
      (fun i => by simpa [read, b, D.raw.tokenBar] using (hN i).1 p x U) v
  · rw [← D.raw.tokenOS]
    exact semilinear_on_basis (read (timeMirror x) U) (read x (timeMirrorLinks U)) (D.raw.os d)
      (fun i => by simpa [read, b, D.raw.tokenOS] using (hN i).2 p x U) v

theorem gradeStencil (D : WilsonData B C) (d : ℕ) :
    ∃ stencil : Finset (Axis → ℤ), ∀ N p (x : Site (C.period p * C.denominator N)),
      let sites := stencil.image fun z => (fun i => (z i : ZMod (C.period p * C.denominator N).val)) + x
      ∀ U V, (∀ e, e.1 ∈ sites → e.1 + Pi.single e.2 1 ∈ sites → U e = V e) →
        ∀ v : RawSpace (D.raw.width d),
          C.insertion N p (D.raw.token ⟨d,v⟩) x U = C.insertion N p (D.raw.token ⟨d,v⟩) x V := by
  classical
  let b := Pi.basisFun ℂ (Fin (D.raw.width d))
  choose stencil basisLocal using fun i : Fin (D.raw.width d) =>
    D.regular.localSupport (D.raw.token ⟨d,b i⟩)
  refine ⟨Finset.univ.biUnion stencil, ?_⟩
  intro N p x sites U V agree v
  let lhs := (D.raw.linear N p d x U).mk' _
  let rhs := (D.raw.linear N p d x V).mk' _
  apply LinearMap.congr_fun (f := lhs) (g := rhs) _ v
  apply b.ext
  intro i
  apply basisLocal i N p x U V
  have sub : stencil i ⊆ Finset.univ.biUnion stencil :=
    Finset.subset_biUnion_of_mem stencil (Finset.mem_univ i)
  exact fun e ha hb => agree e (Finset.image_mono _ sub ha) (Finset.image_mono _ sub hb)

theorem AdjointOn.sameTokenGrade {D : WilsonData B C} {T T' : Hierarchy C}
    (h : D.AdjointOn T) (h' : D.AdjointOn T') (u : C.Token) :
    (T.project u).1 = (T'.project u).1 := by
  obtain ⟨⟨d,v⟩, rfl⟩ := D.raw.onto u
  obtain ⟨π,eqn⟩ := h.quotient d
  obtain ⟨π',eqn'⟩ := h'.quotient d
  rw [eqn, eqn']

end WilsonData

end YangMills.Wilson
