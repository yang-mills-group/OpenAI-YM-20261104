import YM.Integration.WilsonMarkedOrdinaryCableSalary
import YM.WilsonCoeffUV.Winding.Spin

/-! Angular evaluation of an ordinary product on one consistent system of
relative lifts. Each proper connected factor stays on those same lifts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedOrdinaryLocalConvolution
open Function Finset Lattice RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open scoped Classical BigOperators

variable {U T V:Type}[NormedAddCommGroup V]{δ A B C:ℝ}{r:ℕ}

def Node (good:U→ Prop)(fold:U→ T)(δ A:ℝ)(P:Ten V T r)(Q:Ten V U r):Prop:=
  ∀x:Fin r→ U,(∀i,good (x i)) → Pore (P (fold ∘ x)) (Q x) A A δ

private theorem raise {x y:V}(h:Pore x y A A δ)(inc:A≤B)(rate:0≤δ):Pore x y B B δ:=
  ⟨h.nearC.trans inc,h.farC.trans inc,h.gap.trans (mul_le_mul_of_nonneg_right inc rate)⟩

theorem Node.more {good:U→ Prop}{fold:U→ T}{P:Ten V T r}{Q:Ten V U r}
    (read:Node good fold δ A P Q)(inc:A≤B)(rate:0≤δ):Node good fold δ B P Q:=
  fun x hx=>raise (read x hx) inc rate

theorem Node.zero (good:U→ Prop)(fold:U→ T)(δ:ℝ):
    Node good fold δ 0 (0:Ten V T r) (0:Ten V U r):=by
  intro x hx;exact ⟨by simp,by simp,by simp⟩

theorem Node.sum {L:Type}(z:Finset L)(P:L→ Ten V T r)(Q:L→ Ten V U r)(cost:L→ ℝ)
    {good:U→Prop}{fold:U→T}(hs:∀j∈z,Node good fold δ (cost j) (P j) (Q j)):
    Node good fold δ (∑j∈z,cost j) (∑j∈z,P j) (∑j∈z,Q j):=by
  intro x hx
  simp only [Finset.sum_apply]
  have each:=fun j h=>hs j h x hx
  refine ⟨(norm_sum_le ..).trans (Finset.sum_le_sum fun j h=>(each j h).nearC),
    (norm_sum_le ..).trans (Finset.sum_le_sum fun j h=>(each j h).farC),?_⟩
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j h=>(each j h).gap)

variable [NormedSpace ℝ V]
theorem Node.scale {good:U→Prop}{fold:U→T}{P:Ten V T r}{Q:Ten V U r}
    (read:Node good fold δ A P Q)(c:ℝ):Node good fold δ (‖c‖*A) (c•P) (c•Q):=by
  intro x hx
  have q:=read x hx
  refine ⟨?_,?_,?_⟩
  · rw [Pi.smul_apply,norm_smul];exact mul_le_mul_of_nonneg_left q.nearC (norm_nonneg _)
  · rw [Pi.smul_apply,norm_smul];exact mul_le_mul_of_nonneg_left q.farC (norm_nonneg _)
  · rw [Pi.smul_apply,Pi.smul_apply,←smul_sub,norm_smul,mul_assoc];exact mul_le_mul_of_nonneg_left q.gap (norm_nonneg _)

theorem Node.spin {good:U→Prop}{fold:U→T}{P:Ten V T r}{Q:Ten V U r}
    (read:Node good fold δ A P Q):Node good fold δ A (swirl P) (swirl Q):=by
  classical
  let n:ℝ:=Fintype.card (Equiv.Perm (Fin r))
  have hn:0<n:=by dsimp [n];positivity
  have combined:=Node.sum (δ:=δ) (good:=good) (fold:=fold) (Finset.univ:Finset (Equiv.Perm (Fin r)))
    (fun j x=>P (x ∘ j)) (fun j x=>Q (x ∘ j)) (fun _=>A)
    (fun j _ x hx=>read (x ∘ j) (fun i=>hx (j i)))
  have cost:‖n⁻¹‖*(∑_j:Equiv.Perm (Fin r),A)=A:=by
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le),Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact inv_mul_cancel_left₀ hn.ne' A
  change Node good fold δ A (n⁻¹•_) (n⁻¹•_)
  rw [←cost];exact combined.scale n⁻¹

variable {ι:Type}[DecidableEq ι]{D:ι→ℕ}{J S:Finset ι}

theorem Node.product {good:U→Prop}{fold:U→T}{i j:ℕ}(h:J⊆S){P:Ten (Pen D J) T i}{Q:Ten (Pen D J) U i}
    {X:Ten (Pen D (S\J)) T j}{Y:Ten (Pen D (S\J)) U j}
    (first:Node good fold δ A P Q)(second:Node good fold δ B X Y)(a:0≤A)(b:0≤B):
    Node good fold δ (2*(A*B)) (cobT h P X (i+j)) (cobT h Q Y (i+j)):=by
  intro x hx
  have p:=first (x ∘ Fin.castAdd j) (fun u=>hx _)
  have q:=second (x ∘ Fin.natAdd i) (fun u=>hx _)
  have hA:0≤A*B:=mul_nonneg a b
  have z:=p.joins h q
  simp only [cobT,Fin.cast_refl,id_comp]
  exact ⟨z.nearC.trans (by linarith),z.farC.trans (by linarith),z.gap.trans_eq (by ring)⟩

end YM.Integration.WilsonMarkedOrdinaryLocalConvolution
end
