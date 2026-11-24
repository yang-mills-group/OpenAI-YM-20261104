import YM.Integration.WilsonReportHarvestReplayRoom

/-! Distance allocated to the original dated source. The extra support
pays all measured backward-temperature factors from its birth to the
upper retained field, including the short interval before admission. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayReach
open Filter Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonMeasuredAdmission WilsonReportHarvestSourceReach
open scoped Topology
variable {G:Gauge}
def required (A:Levels G)(c t:ℝ)(E n m j:ℕ):ℕ:=
  reach A c t m j + depth A (↑(E*(j-n+1):ℕ)) 1 j

private theorem dated {G:Gauge}{C:Family G} (n m j K:ℕ)(nm:n ≤ m)(mj:m ≤ j)
    (prior:((m-n:ℕ):ℝ)  ≤  (K:ℝ)*(1+Real.log (mast C.path.levels m))):
    ((j-n+1:ℕ):ℝ)  ≤  ((K:ℝ)+1)*(1+Real.log (mast C.path.levels m))*(1+elapsed C.S m j) := by
  let v:=1+Real.log (mast C.path.levels m)
  let e:=elapsed C.S m j
  have v1:1 ≤ v:=by dsimp only [v];linarith only [Real.log_nonneg (mast_gt_one C.path.levels m).le]
  have e0:0 ≤ e:=sub_nonneg.mpr ((OPE.scale_mono C.S).monotone mj)
  have steps:=RG05Readout.Many.tall (C:=C) m j mj
  change ((j-m:ℕ):ℝ) ≤ e at steps
  have count:j-n+1=(j-m)+(m-n)+1:=by omega
  rw [count,Nat.cast_add,Nat.cast_add,Nat.cast_one]
  calc _  ≤  (1+e)+(K:ℝ)*v:=by dsimp only [v] at *;linarith only [steps,prior]
       _  ≤  v*(1+e)+(K:ℝ)*(v*(1+e)):=add_le_add (le_mul_of_one_le_left (by linarith) v1)
          (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) (by linarith)) (Nat.cast_nonneg K))
       _ = _:=by change _=((K:ℝ)+1)*v*(1+e);ring

private theorem grow (A:Levels G){m j:ℕ}(mj:m ≤ j)(slope:G.slopeConstant ≤ A.clock.hatBeta m):
    mast A j  ≤  mast A m*(1+elapsed A.S m j):=by
  let e:=elapsed A.S m j
  let T:=A.clock.hatBeta
  have e0:0 ≤ e:=sub_nonneg.mpr ((OPE.scale_mono A.S).monotone mj)
  have lo:0<T m:=zero_lt_one.trans (A.fits.delayed m)
  have hi:0<T j:=zero_lt_one.trans (A.fits.delayed j)
  have diff:=Real.log_le_sub_one_of_pos (div_pos hi lo)
  rw [Real.log_div hi.ne' lo.ne'] at diff
  have clock:T j-T m=G.slopeConstant*e:=by
    dsimp only [T,e,elapsed,Calendar.hatBeta]
    change _+_*(A.S.scale j)-(_+_*(A.S.scale m))=_*(A.S.scale j-A.S.scale m)
    ring
  have step:T j/T m-1 ≤ e:=by
    rw [div_sub_one lo.ne',(div_le_iff₀ lo),clock,mul_comm e]
    exact mul_le_mul_of_nonneg_right slope e0
  calc mast A j  ≤  mast A m+e:=by change 2+Real.log (T j)  ≤  2+Real.log (T m)+e;linarith only [diff,step]
       _  ≤  _:=by change _ ≤ mast A m*(1+e);nlinarith only [mul_nonneg (sub_nonneg.mpr (mast_gt_one A m).le) e0]

theorem housing (R:Run G)(simple:G.Simple){c t:ℝ}(cp:0 ≤ c)(tp:0 ≤ t)(E K:ℕ):
    ∀ᶠm:ℕ in atTop,∀n:ℕ,n ≤ m → ((m-n:ℕ):ℝ) ≤ (K:ℝ)*(1+Real.log (mast R.family.path.levels m)) →
      ∀j:ℕ,∀mj:m ≤ j,∀per:ℕ,let A:=R.family.path.levels
      let B:=(A.budget j).B
      required A c t E n m j*(4*B+2)+2*B  ≤  (R.family.S.toDepth mj per).count.val*(A.budget m).B^2:=by
  let k:ℝ:=(10*c+15)+(10*t+15)+(10*(E:ℝ)*((K:ℝ)+1)+15)
  have kp:0<k:=by dsimp only [k];positivity
  filter_upwards [WilsonReportHarvestReplayRoom.original R simple kp,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop G.slopeConstant]
    with m room slope n nm prior j mj per A B
  let X:=mast A m
  let x:=mast A j
  let e:=elapsed A.S m j
  let v:=1+Real.log X
  let u:=1+e
  let W:=v*u
  have x1:1 ≤ x:=(mast_gt_one A j).le
  have X1:1 ≤ X:=(mast_gt_one A m).le
  have v1:1 ≤ v:=by dsimp only [v];linarith only [Real.log_nonneg X1]
  have e0:0 ≤ e:=sub_nonneg.mpr ((OPE.scale_mono A.S).monotone mj)
  have u1:1 ≤ u:=by dsimp only [u];linarith only [e0]
  have uW:u ≤ W:=le_mul_of_one_le_left (zero_le_one.trans u1) v1
  have W1:1 ≤ W:=u1.trans uW
  have W0:0 ≤ W:=zero_le_one.trans W1
  have x0:0 ≤ x:=zero_le_one.trans x1
  let D:=depth A c 1 j
  let H:=depth A (t*e) 0 j
  let J:=depth A (↑(E*(j-n+1):ℕ)) 1 j
  let amount:=((E*(j-n+1):ℕ):ℝ)
  have thick:amount  ≤  ((E:ℝ)*((K:ℝ)+1))*W:=by
    dsimp only [amount,W,v,u,X,e]
    rw [Nat.cast_mul]
    calc _  ≤  (E:ℝ)*(((K:ℝ)+1)*(1+Real.log (mast A m))*(1+elapsed A.S m j)):=
               mul_le_mul_of_nonneg_left (dated n m j K nm mj prior) (Nat.cast_nonneg E)
         _ = _:=by ring
  have span:e ≤ W:=(by dsimp only [u];linarith:e ≤ u).trans uW
  have oldA:=WilsonReportHarvestSourceReach.cost A j 1 cp
  have oldB:=WilsonReportHarvestSourceReach.cost A j 0 (mul_nonneg tp e0)
  have newA:=WilsonReportHarvestSourceReach.cost A j 1 (show 0 ≤ amount by positivity)
  change ((D*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(c+1)+5)*x^3 at oldA
  change ((H*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(t*e+1)+5)*x^2 at oldB
  change ((J*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(amount+1)+5)*x^3 at newA
  have bill₁:(10*(c+1)+5)*x^3  ≤  (10*c+15)*(W*x^3):=by
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg x0 _)
    nlinarith only [mul_nonneg (show 0 ≤ 10*c+15 by positivity) (sub_nonneg.mpr W1)]
  have bill₂:(10*(t*e+1)+5)*x^2  ≤  (10*t+15)*(W*x^3):=by
    rw [←mul_assoc]
    exact mul_le_mul (by nlinarith only [mul_le_mul_of_nonneg_left span tp,W1])
      (pow_le_pow_right₀ x1 (by decide : 2 ≤ 3)) (sq_nonneg _) (by positivity)
  have bill₃:(10*(amount+1)+5)*x^3  ≤  (10*(E:ℝ)*((K:ℝ)+1)+15)*(W*x^3):=by
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg x0 _)
    nlinarith only [thick,W1]
  have counts:required A c t E n m j*(4*B+2)+2*B  ≤ 
      (D*(4*B+2)+2*B+1)+(H*(4*B+2)+2*B+1)+(J*(4*B+2)+2*B+1):=by
    change (D+H+J)*(4*B+2)+2*B ≤ _;rw [Nat.add_mul,Nat.add_mul];omega
  have scale:=grow A mj slope
  have factor:W*x^3  ≤  (X^3*(1+Real.log X))*(1+e)^4:=calc
    _  ≤  W*(X*u)^3:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ x0 scale 3) W0
    _ = _:=by dsimp only [W,u,v];ring
  have target:=room j mj per
  have cast:((required A c t E n m j*(4*B+2)+2*B:ℕ):ℝ)  ≤ 
      (((A.S).toDepth mj per).count.val:ℝ)*((A.budget m).B:ℝ)^2:=calc
    _  ≤  ((D*(4*B+2)+2*B+1:ℕ):ℝ)+((H*(4*B+2)+2*B+1:ℕ):ℝ)+((J*(4*B+2)+2*B+1:ℕ):ℝ):=by exact_mod_cast counts
    _  ≤  k*(W*x^3):=by dsimp only [k];linarith only [oldA.trans bill₁,oldB.trans bill₂,newA.trans bill₃]
    _  ≤  k*((X^3*(1+Real.log X))*(1+e)^4):=mul_le_mul_of_nonneg_left factor kp.le
    _  ≤  _:=by simpa only [mul_assoc] using target
  exact_mod_cast cast

end YM.Integration.WilsonReportHarvestReplayReach
