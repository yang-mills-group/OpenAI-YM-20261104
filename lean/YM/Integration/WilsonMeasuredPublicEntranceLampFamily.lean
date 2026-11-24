import YM.Integration.WilsonMeasuredPublicEntranceOwner
import YM.Integration.WilsonOriginalScalarGallery

/-! Join the marked ordinary entries of an arbitrary finite set on one actual
receiver. Each input index has its own injective inclusion, preserving the
mode, address, clear mark and full unmasked function. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceLampFamily
open Function Finset Lattice Wilson RG Marker QuadraticLocal
open scoped Classical BigOperators
variable {G : Gauge} {T V : Type} [DecidableEq V] {n : Side}
    (W : Rep G n) (o : V → Site n) (J : Census V)

def Kept {I E : Type} (input : Lamps T I G W.p o J) (out : Lamps T E G W.p o J) : Prop :=
  ∃ key : I → E, Injective key ∧ ∀ i, out.mode (key i) = input.mode i ∧
    out.address (key i) = input.address i ∧ out.clear (key i) = input.clear i ∧
    ∀x, out.nominal x (key i) = input.nominal x i

private theorem only {I : Type} (A : Lamps T I G W.p o J) (v : V) (id : ∀i,A.mode i=J.fire v)
    (x : T) (U : Config G n) (sums : Summable fun i => A.frame i x U) :
    A.log x U=Poly.send (J.fire v) ((A.log x U).part (J.fire v)) := by
  ext1 s
  by_cases eq : s=J.fire v
  · simp [eq,Poly.part_send]
  · rw [Poly.part_send,if_neg eq,Lamps.log,Poly.share sums]
    simp only [Lamps.frame,Poly.part_send,id,if_neg eq,tsum_zero]

theorem original {I : V→Type} [∀v,Countable (I v)] (A : (v : V)→ Lamps T (I v) G W.p o J)
    (w : V→ℝ) (wp : ∀i,0<w i) (α : ℝ) (positive : 0≤α) (C : V→ℝ)
    (paid : ∀v,(A v).Paid w W.p.B α (C v)) (id : ∀v i,(A v).mode i=J.fire v)
    (input : T→ Config G n → V→ℂ)
    (read : ∀v x U,((A v).log x U).part (J.fire v)=input x U v) (pan : Finset V) :
    ∃ (E : Type) (_ : Countable E) (out : Lamps T E G W.p o J),
      out.Paid w W.p.B α (∑v∈pan,C v) ∧
      (∀x U,out.log x U=∑v∈pan,Poly.send (J.fire v) (input x U v)) ∧
      ∀v∈pan,Kept W o J (A v) out := by
  classical
  induction pan using Finset.induction_on with
  | empty =>
    refine ⟨Empty,inferInstance,WilsonOriginalScalarGallery.empty W o J T,?_,?_,by simp⟩
    · refine ⟨fun i => i.elim,fun i => i.elim,fun i => i.elim,?_⟩
      intro u
      exact ⟨fun i => i.elim,(hasSum_fintype _).summable,by simp⟩
    · intro x U
      simp [Lamps.log]
  | @insert v pan new prior =>
    obtain ⟨E,inst,out,charge,old,retained⟩ := prior
    letI : Countable E := inst
    refine ⟨I v⊕E,inferInstance,(A v).join out,?_,?_,?_⟩
    · simpa only [Finset.sum_insert new] using Lamps.joinPaid (paid v) charge
    · intro x U
      have s := (paid v).sums positive wp x U
      rw [Finset.sum_insert new,Lamps.joinLog _ _ s (charge.sums positive wp x U),old,
        only W o J (A v) v (id v) x U s,read]
    · intro u hu
      rcases Finset.mem_insert.mp hu with eq | prev
      · subst u
        exact ⟨Sum.inl,Sum.inl_injective,fun _ => ⟨rfl,rfl,rfl,fun _ => rfl⟩⟩
      · obtain ⟨e,inj,kept⟩ := retained u prev
        exact ⟨Sum.inr ∘ e,Sum.inr_injective.comp inj,kept⟩

end YM.Integration.WilsonMeasuredPublicEntranceLampFamily
end
