import YM.Integration.WilsonOriginalSignedPhysicalCorridor

/-! Fixed restoration before increasing the ordinary face precision. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOrdinaryFaceOrder
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Multi
open WilsonOriginalMountedRegular WilsonOriginalOrdinaryFlatHulls
open scoped Classical BigOperators

variable {V:Type}[DecidableEq V]{J:Census V}

def constant (s:J.Mode)(n:ℕ):ℝ:=((shards J s).card:ℝ)*((n:ℝ)+2)*3^n

theorem original (s:J.Mode)(n D P:ℕ)(live:s.val.card ≤ n)(parts:∀t∈shards J s,t.val.card ≤ n)
    {g M δ prob:ℝ}(gp:0<g)(gs:g ≤ 1)(mp:0 ≤ M)(debt:M ≤ (g^D)⁻¹)
    (dp:0 ≤ δ)(tiny:δ ≤ g^(P+D*n))(pp:0 ≤ prob)(event:prob ≤ g^(P+D*n)):
    WilsonOriginalOrdinaryFlatHulls.change s M δ+2*cost s M*prob ≤ constant s n*g^P:=by
  let z:ℝ:=(g^D)⁻¹
  have gz:1 ≤ z:=one_le_inv₀ (pow_pos gp D) |>.mpr (pow_le_one₀ gp.le gs)
  have small:δ ≤ 1:=tiny.trans (pow_le_one₀ gp.le gs)
  have restore:z^n*g^(P+D*n)=g^P:=by
    dsimp [z];rw [pow_add,pow_mul,inv_pow];field_simp
  have grows (w:ℕ)(cap:w ≤ n):
      (1+M+δ)^w ≤ (3:ℝ)^n*z^n:=by
    calc
      _ ≤ (3*z)^w:=pow_le_pow_left₀ (by positivity) (by change M ≤ z at debt;linarith) _
      _ ≤ (3*z)^n:=pow_le_pow_right₀ (by linarith) cap
      _ = _:=mul_pow .. 
  have reg (w:ℕ)(cap:w ≤ n):
      (w:ℝ)*δ*(1+M+δ)^w ≤ (n:ℝ)*g^(P+D*n)*((3:ℝ)^n*z^n):=by
    have wc:(w:ℝ) ≤ n:=by exact_mod_cast cap
    exact mul_le_mul (mul_le_mul wc tiny dp (by positivity)) (grows w cap) (by positivity) (by positivity)
  have healthy:WilsonOriginalOrdinaryFlatHulls.change s M δ ≤
      ((shards J s).card:ℝ)*((n:ℝ)*g^(P+D*n)*((3:ℝ)^n*z^n)):=by
    unfold WilsonOriginalOrdinaryFlatHulls.change
    calc
      _ ≤ ∑t∈shards J s,((n:ℝ)*g^(P+D*n)*((3:ℝ)^n*z^n)):=sum_le_sum fun t ht=>reg _ (parts t ht)
      _ = _:=by simp
  have powBound:(1+M)^s.val.card ≤ (3:ℝ)^n*z^n:=
    (pow_le_pow_left₀ (by positivity) (by linarith:1+M ≤ 1+M+δ) _).trans (grows _ live)
  have rough:2*cost s M*prob ≤ 2*((shards J s).card:ℝ)*((3:ℝ)^n*z^n)*g^(P+D*n):=by
    unfold cost
    rw [←mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left powBound (by positivity)) event pp (by positivity)
  calc
    _ ≤ _:=add_le_add healthy rough
    _ = constant s n*(z^n*g^(P+D*n)):=by unfold constant;ring
    _ = _:=by rw [restore]

end YM.Integration.WilsonOriginalOrdinaryFaceOrder
end
