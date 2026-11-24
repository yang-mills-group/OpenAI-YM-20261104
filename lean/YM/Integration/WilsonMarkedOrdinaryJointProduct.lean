import YM.Integration.WilsonMarkedOrdinaryLocalConvolution

/-! Finite and covered Wick sheets on the same set of angular addresses. The
complete degree split and angular symmetrization precede the comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedOrdinaryJointProduct
open Function Finset Lattice RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonMarkedOrdinaryLocalConvolution
open scoped Classical BigOperators

variable {U T V:Type}[NormedAddCommGroup V]{δ A B:ℝ}{r E R:ℕ}
variable {good:U→Prop}{fold:U→T}
def Sheet (good:U→Prop)(fold:U→T)(E R:ℕ)(δ A:ℝ)(P:Pal V T)(Q:Pal V U):Prop:=
  ∀i≤E,∀r≤R,Node good fold δ A (P i r) (Q i r)

private theorem flatSum {X:Type}(z:Finset X)(P:X→Ten V T r)(Q:X→Ten V U r)
    (earned:∀x∈z,Node good fold δ A (P x) (Q x)):
    Node good fold δ ((z.card:ℝ)*A) (∑x∈z,P x) (∑x∈z,Q x):=by
  simpa only [Finset.sum_const,nsmul_eq_mul] using
    (Node.sum z P Q (fun _=>A) earned)

variable {ι:Type}[DecidableEq ι]{D:ι→ℕ}{J S:Finset ι}{i:ℕ}

def gross (E R:ℕ):ℝ := ((E+1:ℕ):ℝ)*(R+1:ℕ)*2

theorem product (h:J⊆S){P:Pal (Pen D J) T}{Q:Pal (Pen D J) U}
    {X:Pal (Pen D (S\J)) T}{Y:Pal (Pen D (S\J)) U}(first:Sheet good fold E R δ A P Q)
    (second:Sheet good fold E R δ B X Y)(a:0≤A)(b:0≤B)(rate:0≤δ):
    Sheet good fold E R δ (gross E R*(A*B)) (foam h P X) (foam h Q Y):=by
  intro i hi r hr
  have angular (j:ℕ×ℕ)(w:j∈Finset.HasAntidiagonal.antidiagonal i):
      Node good fold δ (((r+1:ℕ):ℝ)*(2*(A*B))) (cob h (P j.1) (X j.2) r) (cob h (Q j.1) (Y j.2) r):=by
    have split: j.1 + j.2=i:=Finset.HasAntidiagonal.mem_antidiagonal.mp w
    apply Node.spin
    have v:=flatSum (Finset.HasAntidiagonal.antidiagonal r)
      (fun t=>cobT h (P j.1 t.1) (X j.2 t.2) r) (fun t=>cobT h (Q j.1 t.1) (Y j.2 t.2) r)
      (A:=2*(A*B)) (δ:=δ) (good:=good) (fold:=fold) (fun t ht=>by
        obtain ⟨x,y⟩:=t
        have s:x+y=r:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
        subst r;exact Node.product h (first _ (by omega) _ (by omega)) (second _ (by omega) _ (by omega)) a b)
    simpa only [Finset.Nat.card_antidiagonal] using v
  have c:=flatSum (Finset.HasAntidiagonal.antidiagonal i) _ _ angular
  simp only [foam,Finset.sum_apply]
  apply c.more _ rate
  rw [Finset.Nat.card_antidiagonal]
  unfold gross
  have s:0≤2*(A*B):=by positivity
  calc ((i+1:ℕ):ℝ)*(((r+1:ℕ):ℝ)*(2*(A*B))) ≤ ((E+1:ℕ):ℝ)*(((R+1:ℕ):ℝ)*(2*(A*B))) := by gcongr
       _ = _ := by ring

end YM.Integration.WilsonMarkedOrdinaryJointProduct
end
