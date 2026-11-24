import YM.Integration.WilsonIndependentSpoutAtomicPolar

/-! Rendering a finite raw row commutes with the actual ordered-coordinate
permutation and with including the fine parent in a joint physical board. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFinitePrinting
open Function PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Prim RegulatorIR.Diagram
open WilsonIndependentSpoutAtomicPolar (held)
open scoped Classical BigOperators
variable {I J:Type}[Fintype I][Fintype J]

theorem exact {T:Ranked I}{k:ℕ}(h:Within k T):
    totalR T=packed T k:=by
  apply MvPolynomial.funext
  intro x
  have cap r (hr:k<r):T r=0:=Classical.not_not.mp fun nz=>not_le_of_gt hr (h r nz)
  exact (held (Equiv.refl I) T k cap x).symm.trans (speaking x T k)

theorem move (σ:I≃J){T:Ranked I}{k:ℕ}(h:Within k T):
    totalR (fun r q=>T r (σ.symm∘q))=MvPolynomial.rename σ (packed T k):=by
  apply MvPolynomial.funext;intro y
  have cap r (hr:k<r):(fun q:Tuple J r=>T r (σ.symm∘q))=0:=by
    have dz:T r=0:=Classical.not_not.mp fun nz=>not_le_of_gt hr (h r nz)
    rw [dz];rfl
  have hk:=held σ (fun r q=>T r (σ.symm∘q)) k cap y
  have same:(fun r q=>T r (σ.symm∘(σ ∘ q)))=T:=by
    funext r q;apply congrArg (T r);funext j;exact σ.symm_apply_apply (q j)
  rw [same] at hk
  rw [MvPolynomial.eval_rename,←speaking]
  exact hk.symm

theorem left (T:Ranked I){k:ℕ}(h:Within k T):
    totalR (fun r=>offer (Function.Embedding.inl (α:=I) (β:=J)) (T r))=
      MvPolynomial.rename (Sum.inl:I→I⊕J) (totalR T):=by
  apply MvPolynomial.funext;intro x
  let a: I↪I⊕J:=Function.Embedding.inl
  have scope:Within k (fun r=>offer a (T r)):=by
    intro r hn;apply h r;intro hz;apply hn;ext1 q;simp [offer,Stalk.collect,hz]
  change MvPolynomial.eval x (totalR (fun r=>offer a (T r)))=_
  rw [exact scope,MvPolynomial.eval_rename,exact h]
  rw [←speaking,←speaking]
  unfold drums
  exact Finset.sum_congr rfl fun r _=>ample x a (T r)

end YM.Integration.WilsonIndependentSpoutFinitePrinting
