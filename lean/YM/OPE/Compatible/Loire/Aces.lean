import YM.OPE.Compatible.Loire.Wool
/-!
# Homogeneous cubic
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Libra PertExtension Series GaussianScore Flock Nestle Balsam
open scoped BigOperators Classical ContDiff
variable {I V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V] {s:ℝ}{f:V→ℝ}
abbrev Temple (E:Type)[AddCommGroup E][Module ℝ E]:=E →ₗ[ℝ] E→ₗ[ℝ]E→ₗ[ℝ]ℝ
abbrev Trill (A:Temple V):=fun x=> A x x x
def bishops (A: Temple V)(a b c:V):= A a b c+A a c b+A b a c+A b c a + A c a b + A c b a
omit [FiniteDimensional ℝ V] in
lemma trill_neg (A:Temple V) (x:V): Trill A (-x) = -(Trill A x):=by simp [Trill]
lemma on_line (z:V)(hf:Bond f)(x:V){p:ℝ}(hp:HasDerivAt (fun i:ℝ=>f (x+i • z)) p 0):poke z f x=p:=by
   have he : HasDerivAt (fun i:ℝ=>f (x+i • z)) (poke z f x) 0:=by
       have hx : x+ (0:ℝ) • z=x:=by simp
       convert! HasFDerivAt.comp_hasDerivAt 0 (f:=fun i:ℝ=>x+i • z) (hf.smooth.differentiable (by simp) (x+ (0:ℝ) • z)|>.hasFDerivAt) (show HasDerivAt (fun i:ℝ=>x+i•z) z 0 by simpa using HasDerivAt.const_add x ((hasDerivAt_id' (0:ℝ)).smul_const z)) using 1 -- hx rewrite
       rw [hx]; rfl
   exact he.unique hp
lemma poke_triple (A:Temple V)(z:V)(hp:Bond (Trill A)): poke z (Trill A)=(fun x=>A z x x+A x z x+A x x z):=by
   funext x; apply on_line z hp x; simp only [Trill,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,mul_add]; -- explicit differentiability.Eval via `convert t pow deriv`
   convert! Hfn (a:=Trill A x) (b:=A z x x+A x z x+A x x z) (c:=A z z x+A z x z+A x z z) (d:=Trill A z) using 2 with i; unfold Trill; ring
where Hfn {a b c d:ℝ}:HasDerivAt (fun i:ℝ=> a+b*i+c*i^2+d*i^3) b 0:=by
        have hc(k:ℕ):= (hasDerivAt_pow k (0:ℝ)); convert! (((HasDerivAt.const_add a ((hasDerivAt_id' (0:ℝ)).const_mul b)).add ((hc 2).const_mul c)).add ((hc 3).const_mul d)) using 1; simp
lemma pokes_two (A:Temple V)(y z:V)(hp:Bond (Trill A)): poke z (poke y (Trill A)) = (fun x=>bishops A y z x):=by
   have he:= hp.amount y; change Bond (poke y (Trill A)) at he; rw [poke_triple _ _ hp] at he ⊢; funext x; apply on_line z he x; simp_rw [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]; convert! Hfn (a:=A y x x+A x y x+A x x y) (b:= bishops A y z x) (c:=A y z z+A z y z+A z z y) using 2 with i; unfold bishops; simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];ring
where Hfn {a b c:ℝ}:HasDerivAt (fun i:ℝ=> a+b*i +c*i^2) b 0:=by convert! (HasDerivAt.const_add a ((hasDerivAt_id' (0:ℝ)).const_mul b) |>.add ((hasDerivAt_pow 2 (0:ℝ)).const_mul c)) using 1; simp
lemma poke_hr (A:Temple V)(x y z:V)(hp:Bond (Trill A)): poke z (poke y (poke x (Trill A))) = fun _=> bishops A x y z:=by
    have he:= (hp.amount x).amount y; change Bond (poke y (poke x (Trill A))) at he; funext t; apply on_line _ he _; rw [pokes_two _ _ _ hp]; dsimp only; rw [show (fun i=> bishops A x y (t+i • z))=(fun i:ℝ=>bishops A x y t+bishops A x y z*i) from funext fun i=>by unfold bishops; simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];ring]; simpa using HasDerivAt.const_add (bishops A x y t) ((hasDerivAt_id' (0:ℝ)).const_mul (bishops A x y z))
end YM.OPE.Shrew
