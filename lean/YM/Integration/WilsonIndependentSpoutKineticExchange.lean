import YM.Integration.WilsonIndependentSpoutUnmarkedClock

/-! The exact reflection exchanging two parallel links carrying the
same color component on the genuine propagated cover action. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutKineticExchange
open Lattice Exterior WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}

private def invert:Signed:=⟨Equiv.refl _,fun _=>true⟩

private lemma reflected (z x:Cover):
    ringS invert (z+step 1) (x,1)=(z-x,1) := by
  have H:invert.act x= -x := by funext j;rfl
  unfold ringS affine
  rw [H]
  change (-x+(z+step 1)-step 1,(1:Axis))=(z-x,1)
  congr 1;abel

theorem actual {P:Canvas G}(H:swing P)(e:ℕ)(z:Cover)(c:G.ColorIndex):
    P e 2 ![stone (z,1) c,stone (0,1) c] =
    P e 2 ![stone (0,1) c,stone (z,1) c] := by
  let q:Fin 2 → YForest G:=![stone (0,1) c,stone (z,1) c]
  have edge:tickW invert (z+step 1) ∘ q=![stone (z,1) c,stone (0,1) c]:=by
    funext i;fin_cases i <;> simp [q,Function.comp_apply,tick_stone,reflected]
  have fee:(∏ i,rimSign invert (q i).2)=1:=by simp [rimSign,invert]
  have result:=H invert (z+step 1) e 2 q
  rw [edge,fee,one_mul] at result
  exact result

theorem changed {P:Canvas G}(H:swing P)(α:PowerSeries ℝ):swing (Blue.mix α P) := by
  intro s b e r t
  simp only [Blue.mix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [H s b j r t]
  ring

end YM.Integration.WilsonIndependentSpoutKineticExchange
