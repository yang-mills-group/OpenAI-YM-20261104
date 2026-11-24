import YM.Integration.WilsonThermometerCenteredAlgebra

/-! Compare the complete two ordinary thermometer tables after centering both
by the same filed table.  Only a *difference* of proper residuals needs a
linear coupling estimate.  The original proper residuals may tend to zero at
any rate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedDelta
open Finset Filter Marker QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open scoped BigOperators Classical Topology
local notation "J" => Stock.census (Fin 3)

def rent (P:Poly J):ℝ:=Poly.price (fun _=>1) P
def residue (F W:Poly J):Poly J:=proper (total F W)
def discrepancy (F G W:Poly J):ℂ:=
  (Extra.Trajectories.connected F).part full-(Extra.Trajectories.connected G).part full-
    ((total F W).part full-(total G W).part full)

theorem difference (F G W:Poly J) (fp:F.part (J).quiet=1) (gp:G.part (J).quiet=1)
    (wp:W.part (J).quiet=1):
    let X:=residue F W
    let Y:=residue G W
    discrepancy F G W=
      -(2:ℂ)⁻¹*((X-Y)*(X+Y)).part full+(3:ℂ)⁻¹*((X-Y)*(X^2+X*Y+Y^2)).part full:=by
  dsimp only
  let X:=residue F W
  let Y:=residue G W
  have e₂:(X-Y)*(X+Y)=X^2-Y^2:=by ring
  have e₃:(X-Y)*(X^2+X*Y+Y^2)=X^3-Y^3:=by ring
  change _= -(2:ℂ)⁻¹*((X-Y)*(X+Y)).part full+(3:ℂ)⁻¹*((X-Y)*(X^2+X*Y+Y^2)).part full
  rw [e₂,e₃]
  simp only [sub_eq_add_neg,Poly.part_plus,Poly.part_neg]
  unfold discrepancy
  have a:=WilsonThermometerCenteredAlgebra.connected F W fp wp
  have b:=WilsonThermometerCenteredAlgebra.connected G W gp wp
  change _ = _-(2:ℂ)⁻¹*(X^2).part full + (3:ℂ)⁻¹*(X^3).part full at a
  change _ = _-(2:ℂ)⁻¹*(Y^2).part full + (3:ℂ)⁻¹*(Y^3).part full at b
  linear_combination a-b

private theorem nonneg (X:Poly J):0≤rent X:=Poly.nonnegative (fun _=>zero_lt_one) X
private theorem component (X:Poly J):‖X.part full‖≤rent X:=by
  simpa [rent,Poly.toll] using Poly.member (fun _:Fin 3=>zero_lt_one) full X
private theorem product (X Y:Poly J):rent (X*Y)≤rent X*rent Y:=
  Poly.multiplication (fun _:Fin 3=>zero_lt_one) X Y
private theorem add (X Y:Poly J):rent (X+Y)≤rent X+rent Y:=
  Poly.addition (fun _:Fin 3=>zero_lt_one) X Y

def rate (a b:ℝ):ℝ:=(a+b)/2+(a^2+a*b+b^2)/3

theorem price (F G W:Poly J) (fp:F.part (J).quiet=1) (gp:G.part (J).quiet=1)
    (wp:W.part (J).quiet=1):
    let X:=residue F W
    let Y:=residue G W
    ‖discrepancy F G W‖≤rent (X-Y)*rate (rent X) (rent Y):=by
  let X:=residue F W
  let Y:=residue G W
  change _≤rent (X-Y)*rate (rent X) (rent Y)
  have square (P:Poly J):rent (P^2)≤(rent P)^2:=by simpa only [pow_two] using product P P
  have b₂:=((component ((X-Y)*(X+Y))).trans (product _ _)).trans
    (mul_le_mul_of_nonneg_left (add X Y) (nonneg (X-Y)))
  have tri:rent (X^2+X*Y+Y^2)≤(rent X)^2+rent X*rent Y+(rent Y)^2:=
    (add _ _).trans (add_le_add ((add _ _).trans (add_le_add (square X) (product X Y))) (square Y))
  have b₃:=((component ((X-Y)*(X^2+X*Y+Y^2))).trans (product _ _)).trans
    (mul_le_mul_of_nonneg_left tri (nonneg (X-Y)))
  rw [difference F G W fp gp wp]
  change ‖-(2:ℂ)⁻¹*((X-Y)*(X+Y)).part full+(3:ℂ)⁻¹*((X-Y)*(X^2+X*Y+Y^2)).part full‖≤_
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,norm_neg,norm_inv]
  norm_num [norm_div]
  unfold rate
  linarith only [b₂,b₃]

private theorem positive_rate {x y:ℝ} (hx:0≤x) (hy:0≤y):0≤rate x y:=by unfold rate; positivity

private theorem scaled (F G W:Poly J) (g C:ℝ) (p:0<g)
    (u:F.part (J).quiet=1 ∧ G.part (J).quiet=1 ∧ W.part (J).quiet=1)
    (paid:rent (residue F W-residue G W)≤C*g):
    ‖discrepancy F G W‖/g≤C*rate (rent (residue F W)) (rent (residue G W)):=by
  have hv:=price F G W u.1 u.2.1 u.2.2
  have hx:=nonneg (residue F W)
  have hy:=nonneg (residue G W)
  have hr:=positive_rate hx hy
  apply (div_le_iff₀ p).2
  exact (hv.trans (mul_le_mul_of_nonneg_right paid hr)).trans_eq (by ring)

private theorem rate_zero {I:Type*} {l:Filter I} {a b:I→ℝ}
    (h:Tendsto a l (𝓝 0)) (k:Tendsto b l (𝓝 0)):
    Tendsto (fun i=>rate (a i) (b i)) l (𝓝 0):=by
  have hl:=((h.add k).div_const 2).add ((((h.pow 2).add (h.mul k)).add (k.pow 2)).div_const 3)
  simpa only [rate,zero_add,zero_mul,zero_pow (by decide : 2≠0),zero_div] using hl

theorem small {I:Type*} (l:Filter I) (F G W:I→Poly J) (g:I→ℝ) (C:ℝ)
    (units:∀ᶠi in l,(F i).part (J).quiet=1 ∧ (G i).part (J).quiet=1 ∧ (W i).part (J).quiet=1)
    (pos:∀ᶠi in l,0<g i) (g₀:Tendsto g l (𝓝 0))
    (p₀:Tendsto (fun i=>rent (residue (F i) (W i))) l (𝓝 0))
    (paid:∀ᶠi in l,rent (residue (F i) (W i)-residue (G i) (W i))≤C*g i):
    Tendsto (fun i=>‖discrepancy (F i) (G i) (W i)‖/g i) l (𝓝 0):=by
  let X:=fun i=>residue (F i) (W i)
  let Y:=fun i=>residue (G i) (W i)
  have neg (P:Poly J):rent (-P)=rent P:=by simp [rent,Poly.price]
  have d₀:Tendsto (fun i=>rent (X i-Y i)) l (𝓝 0):=by
    apply squeeze_zero' (Eventually.of_forall fun _=>nonneg _) paid
    simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul g₀
  have y₀:Tendsto (fun i=>rent (Y i)) l (𝓝 0):=by
    apply squeeze_zero' (Eventually.of_forall fun _=>nonneg _) (Eventually.of_forall fun i=>?_)
    · simpa only [add_zero] using p₀.add d₀
    · have h:=add (X i) (-(X i-Y i))
      rw [neg] at h
      simpa only [neg_sub,add_sub_cancel] using h
  have coef:=rate_zero p₀ y₀
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul coef)
  · filter_upwards [pos] with i hi using div_nonneg (norm_nonneg _) hi.le
  · filter_upwards [units,pos,paid] with i u hi P using scaled (F i) (G i) (W i) (g i) C hi u P

end YM.Integration.WilsonMaxwellThermometerNominatedDelta
