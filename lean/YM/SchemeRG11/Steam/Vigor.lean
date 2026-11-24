import YM.SchemeRG11.Steam.Hale

/-! Exact d4 counterpart of vertex Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "X" => Nodes 4

def castEye (x y z:E4) : X := ![x,y,z]
def trio (p : Time) (x : X) := (knot p ^2)⁻¹*Real.exp (-∑ i,fork p i*bevel i x)*base^2
lemma braid_four (μ : ℝ) (p : Time) : braid μ p 0 (n:=4)=Complex.ofRealCLM ∘ trio p := by
  ext1 x; unfold braid; change _=Complex.ofReal (trio p x)
  simp only [trio,base,Complex.cpow_neg,zero_sub,Complex.cpow_ofNat, factor_zero]; push_cast; rfl
lemma trio_diff (p : Time) : ContDiff ℝ ∞ (trio p) := by unfold trio; exact (contDiff_const.mul (ContDiff.exp (ContDiff.neg (ContDiff.sum (fun i _=> contDiff_const.mul (bevel_c i)))))).mul contDiff_const
lemma spin_four (μ : ℝ) (l : Sweep 4) (p : Time) : spin μ l p 0 = Complex.ofRealCLM ∘ series (trio p) l := by
  unfold spin; rw [braid_four,series_c (trio_diff p)]

private lemma square_sum (a b c : ℝ) (δ : ℝ) (hh : δ=a+b+c) (hd : 0<δ) (x y z w : E4) :
    a*‖x-w‖^2+b*‖y-w‖^2+c*‖z-w‖^2=δ*‖w-δ⁻¹•(a • x+b • y+c • z)‖^2+(b*c*‖y-z‖^2+c*a*‖z-x‖^2+a*b*‖x-y‖^2)/δ := by
  simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,real_inner_smul_left,real_inner_smul_right]; field_simp; rw [hh]
  simp only [real_inner_comm y x,real_inner_comm z y,real_inner_comm z x, real_inner_comm w x, real_inner_comm w y, real_inner_comm w z]; ring
lemma expan (p : Time) (x : X) : (∑ i,fork p i*bevel i x)= (p.1*‖x 1-x 2‖^2+p.2.1*‖x 2-x 0‖^2+p.2.2*‖x 0-x 1‖^2)/(4*knot p) := by
  unfold Eye; rw [Fin.sum_univ_three]; unfold fork bevel; change p.1 / _ * (‖x 1-x 2‖^2/4)+p.2.1/knot p * (‖x 2-x 0‖^2/4)+p.2.2/knot p * (‖x 0-x 1‖^2/4)= _; ring

lemma life_four (p : Time) (hp : p∈tripod) (x : X) :
    trio p x=∫ w:E4, gauze p.1 (x 0-w)*gauze p.2.1 (x 1-w)*gauze p.2.2 (x 2-w) := by
  rcases p with ⟨r,s,t⟩
  let A:=α r; let B:=α s; let C:=α t; let K:=A+B+C
  let L := K⁻¹• (A • x 0+B • x 1 + C • x 2)
  let p:Time:=(r,s,t)
  have hr :0<r:=hp.1; have hs:0<s:=hp.2.1; have ht:0<t:=hp.2.2
  have hA :0<A:=by unfold A α; positivity
  have hB :0<B:=by unfold B α; positivity
  have hC: 0<C:=by unfold C α; positivity
  have hK:0<K:= by unfold K; positivity
  have hh : K= (knot p)/(4*r*s*t) := by dsimp [A,B,C,K,α,knot,p]; field_simp; ring
  let E:= - ∑ i,fork p i*bevel i x
  have hq (w:E4) : -(A*‖x 0-w‖^2+B*‖x 1-w‖^2+C*‖x 2-w‖^2)= E + -K*‖w-L‖^2 := by
    rw [square_sum A B C K rfl hK]; unfold E L; rw [expan,hh]
    have he:= Cluster.globe p hp
    have hz : r*s+r*t+s*t > 0:=he
    dsimp [p,knot,A,B,C,α]; field_simp; ring
  let b : ℝ := base^3*((r*s*t)^2)⁻¹
  have hd (w:E4): gauze r (x 0-w)*gauze s (x 1-w)*gauze t (x 2-w)= b*Real.exp E * Real.exp (-K*‖w-L‖^2) := by
    rw [mul_assoc b,←Real.exp_add,hq w|>.symm]; unfold gauze
    simp only [neg_add_rev, Real.exp_add]; change (base*(r^2)⁻¹*Real.exp (-A * _) * (base*(s^2)⁻¹*Real.exp (-B * _))) * (base*(t^2)⁻¹*Real.exp (-C * _)) = _; simp only [neg_mul]; unfold b; ring
  dsimp only; simp_rw [hd]
  rw [integral_const_mul, integral_sub_right_eq_self (fun w:E4=> Real.exp (-K*‖w‖^2)) (μ:=volume) L, GaussianFourier.integral_rexp_neg_mul_sq_norm hK]
  change (knot p^2)⁻¹ * Real.exp E * base^2 = _; have he:=Cluster.globe p hp
  norm_num [hh,b,base,Axis]
  field_simp
end YM.SchemeRG11.Steam
