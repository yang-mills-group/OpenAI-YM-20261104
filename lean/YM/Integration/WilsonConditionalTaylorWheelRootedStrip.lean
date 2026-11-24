import YM.Integration.WilsonVacuumPreResetCanonicalCoil
import YM.Integration.WilsonConditionalTaylorIndependentMarked

/-! Convert the actual rooted exponential estimate of the Wilson
marked field into the independently required summable whole-word
bound, with a positive half strip and a torus-independent cost. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRootedStrip
open Function Filter Lattice Laurent RG Wilson Exterior Precision Tree Bloch
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic
open FormalBulk08 FormalBulk08.Lava Kemp Gorge Lotus Reef Rift
open scoped Classical Topology ENNReal BigOperators
variable {I:Type} {n:Side} {r:ℕ}

theorem distance (x y:Tor n I):(lake n I).d x y=(tor n).gap x.1 y.1:=
  Lotus.skit_sub n x.1 y.1

theorem sites (o:Tor n I) (v:chain (Tor n I) r) (i:Fin (r+1)):
    ((Fin.cons o v : Fin (r+1)→Tor n I) i).1=stud o.1 v i:=by
  refine Fin.cases ?_ (fun t=>?_) i <;> rfl

theorem diameter (o:Tor n I) (v:chain (Tor n I) r):
    Kemp.herb (lake n I) o v=Soil.tread (tor n) o.1 v:=by
  apply le_antisymm
  · apply known_wide
    intro i j
    rw [distance,sites o v i,sites o v j]
    exact leg_le (tor n) (stud o.1 v) i j
  · apply league_le
    intro i j
    rw [←sites o v i,←sites o v j,←distance]
    exact reached (lake n I) (Fin.cons o v) i j

variable [Fintype I]
theorem summation {s C:ℝ} (sPos:0<s) (o:Tor n I) (P:Tile (Tor n I) r)
    (old:Soil.Cork (tor n) o.1 s C P):
    Knoxville (lake n I) (s/2) o P (C*(boardPay I ((s/2)/(max 1 r:ℕ)))^r):=by
  classical
  let t:ℝ:=(s/2)/(max 1 r:ℕ)
  have tPos:0<t:=by dsimp [t];exact div_pos (by linarith) (by exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_max_left 1 r)))
  have term (v:chain (Tor n I) r):
      Real.exp ((s/2)*(Soil.tread (tor n) o.1 v:ℝ))*‖P v‖≤C*sail t (tor n) o.1 v:=by
    let a:=Soil.tread (tor n) o.1 v
    have legs(i:Fin r):(tor n).gap o.1 (v i).1≤a:=by
      exact leg_le (tor n) (stud o.1 v) (0:Fin (r+1)) i.succ
    have take:Real.exp (-(s/2)*(a:ℝ))≤ sail t (tor n) o.1 v:=by
      by_cases hz:r=0
      · subst r
        calc
          _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
          _ = _ := (Finset.prod_eq_one fun i _=>Fin.elim0 i).symm
      · simpa only [t,max_eq_right (by omega:1≤r),sub_zero,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using
          sail_cut (d:=tor n) (σ:=s/2) (η:=0) (v:=0) (l:=a) (Nat.zero_le _) le_rfl (by linarith) (by omega) o.1 v legs
    calc
      _ ≤ Real.exp ((s/2)*(a:ℝ))*(C*Real.exp (-s*(a:ℝ))):=
        mul_le_mul_of_nonneg_left (old.2 v) (Real.exp_pos _).le
      _ = C*Real.exp (-(s/2)*(a:ℝ)):=by rw [mul_left_comm,←Real.exp_add];congr 2;ring
      _ ≤ _:=mul_le_mul_of_nonneg_left take old.1
  refine ⟨mul_nonneg old.1 (pow_nonneg (boardPay_nn (α:=I) tPos) _),?_⟩
  have priced:(∑v:chain (Tor n I) r,Real.exp ((s/2)*(Soil.tread (tor n) o.1 v:ℝ))*‖P v‖)≤C*(boardPay I t)^r:=by
    calc
      _ ≤ ∑v:chain (Tor n I) r,C*sail t (tor n) o.1 v:=Finset.sum_le_sum fun v _=>term v
      _ = C*∑v:chain (Tor n I) r,sail t (tor n) o.1 v:=(Finset.mul_sum ..).symm
      _ ≤ _:=mul_le_mul_of_nonneg_left (train_native (α:=I) tPos o.1 r) old.1
  have encoded:=ENNReal.ofReal_le_ofReal priced
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] at encoded
  rw [tsum_fintype]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun v _=>?_))) encoded
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ofReal_norm]
  change Gorge.shine (s/2) (Kemp.herb (lake n I) o v) * ‖P v‖ₑ=_
  rw [diameter,Gorge.shine]

theorem original {o:Cover} {P:(n:Side)→Tile (Tor n I) r} {Q:Tile (Biglot I) r}
    (actual:Bends o P Q) (a:I):
    ∃η:ℝ,0<η ∧ Kemp.Kalm η (o,a) Q P:=by
  obtain ⟨s,C,hpos,charge⟩:=actual.price
  refine ⟨s/2,by linarith,actual.point, C*(boardPay I ((s/2)/(max 1 r:ℕ)))^r,?_⟩
  filter_upwards [charge] with n hn
  exact summation hpos (drip n (o,a)) (P n) hn

end YM.Integration.WilsonConditionalTaylorWheelRootedStrip
end
