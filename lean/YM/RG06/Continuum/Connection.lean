import YM.RG06.Continuum.Differential
import YM.Gauge.Casimir

/-!
# Physical continuum stencil conventions

Log links `Pexp ∫ g A` transport back. Thus F_ij, the coefficient for
square i j -i -j, has *plus* commutator. Use the same convention for
D_i on adjoint local fields; order of a list is outermost first. Inputs A
and F have dimensions 1 and 2, g is unweighted. Thus (in the unscaled
potential) D-letters cost one each. In unrescaled `H.links` (classical
engineering projection) take g=1. No gauge-field propagator or equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Maxwell
open scoped ContDiff
variable {G:Gauge}

abbrev ColorField (G:Gauge) := E4 → G.Color
abbrev One (G:Gauge) := Axis → ColorField G

/-- Convenient same-group bilinear pairing of fields. -/
def pair (X Y:ColorField G):ColorField G := fun x=>G.ad (X x) (Y x)

lemma skews (X Y:G.Color):G.ad X Y= -G.ad Y X:= by apply G.colorMat_injective; simp
lemma jac (X Y Z:G.Color):G.ad X (G.ad Y Z)=G.ad (G.ad X Y) Z+G.ad Y (G.ad X Z):= by
  rw [Gauge.ad_jacobi, LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply]
  abel

lemma pair_neg (X Y:ColorField G):pair X Y= -pair Y X:= funext fun _=>skews ..
lemma pair_jac (X Y Z:ColorField G):pair X (pair Y Z)=pair (pair X Y) Z + pair Y (pair X Z):=
  funext fun _=>jac ..
lemma pair_add (X Y Z:ColorField G):pair X (Y+Z)=pair X Y+pair X Z:= funext fun _=> map_add (G.ad _) _ _
lemma pair_add₁ (X Y Z:ColorField G):pair (X+Y) Z=pair X Z + pair Y Z:= by
  funext x
  change G.ad (_+_) _=_+_
  rw [map_add]; rfl
lemma pair_minus (X Y:ColorField G):pair X (-Y)= -(pair X Y):= funext fun _=>map_neg (G.ad _) _
lemma pair_minus₁ (X Y:ColorField G):pair (-X) Y= -(pair X Y):= by
  funext x
  change G.ad (-_) _ = -_
  rw [map_neg]; rfl
lemma pair_diff (X Y Z:ColorField G):pair X (Y-Z)=pair X Y - pair X Z:= funext fun _=>map_sub (G.ad _) _ _
lemma pair_diff₁ (X Y Z:ColorField G):pair (X-Y) Z=pair X Z - pair Y Z:= by rw [sub_eq_add_neg,pair_add₁,pair_minus₁,← sub_eq_add_neg]
lemma pair_scale (X Y:ColorField G)(t:ℝ):pair X (t•Y)=t • pair X Y:= funext fun _=>map_smul (G.ad _) t _
lemma pair_scale₁ (X Y:ColorField G)(t:ℝ):pair (t•X) Y=t • pair X Y:= by
  funext x
  change G.ad (t • _) _ = _
  rw [map_smul]; rfl
lemma pair_zero₁ (Y:ColorField G):pair 0 Y=0:= by funext x; change G.ad 0 _=0; simp
lemma pair_zero (Y:ColorField G):pair Y 0=0:= by rw [pair_neg,pair_zero₁]; simp
abbrev ok (f:ColorField G) := ContDiff ℝ ∞ f
lemma pair_smooth {X Y:ColorField G}(hX:ok X)(hY:ok Y): ok (pair X Y):= bilinear_smooth G.ad hX hY
lemma grad_pair (i:Axis){X Y:ColorField G}(hX:ok X)(hY:ok Y):
    grad i (pair X Y) = pair (grad i X) Y + pair X (grad i Y):=d_bilinear G.ad (basis i) hX hY

def strength (g:ℝ)(A:One G)(a b:Axis):ColorField G:=grad a (A b)-grad b (A a)+g • pair (A a) (A b)
def cov (g:ℝ)(A:One G)(a:Axis)(X:ColorField G):ColorField G:=grad a X+g • pair (A a) X
def smooth (A:One G):Prop:=∀ i, ok (A i)
variable (g:ℝ)(A:One G)
lemma cov_add (i:Axis){X Y:ColorField G}(hX:ok X)(hY:ok Y): cov g A i (X+Y) = cov g A i X + cov g A i Y:= by
  simp only [cov,grad_plus _ hX hY,pair_add,smul_add]; abel
lemma cov_neg (i:Axis)(X:ColorField G): cov g A i (-X) = -(cov g A i X):= by rw [cov,cov,grad_minus,pair_minus,smul_neg]; abel
lemma cov_sub (i:Axis){X Y:ColorField G}(hX:ok X)(hY:ok Y): cov g A i (X-Y)=cov g A i X - cov g A i Y:= by
  rw [sub_eq_add_neg,cov_add _ _ (Y := -Y) i hX hY.neg,cov_neg,←sub_eq_add_neg]
lemma cov_scale (i:Axis)(t:ℝ){X:ColorField G}(hX:ok X):cov g A i (t • X)=t • cov g A i X:=by
  rw [cov,cov,grad_scale _ _ hX,pair_scale,smul_comm g t,smul_add]
lemma cov_zero (i:Axis):cov g A i 0=0:= by funext x; simp [cov,pair,grad,Analysis.D,Pi.zero_def]
lemma cov_pair (i:Axis){X Y:ColorField G}(hX:ok X)(hY:ok Y):
    cov g A i (pair X Y) = pair (cov g A i X) Y + pair X (cov g A i Y):= by
  simp only [cov,grad_pair i hX hY,pair_jac (A i) X Y,pair_add,pair_add₁,pair_scale,pair_scale₁,smul_add]; abel
lemma cov_collect {ι:Type*}(s:Finset ι){f:ι→ColorField G}(hf:∀j∈s,ok (f j))(i:Axis):
    cov g A i (∑ j∈s, f j) = ∑ j∈s,cov g A i (f j):= by
  rw [cov,grad_collect _ hf]
  funext x
  simp [Finset.sum_apply,cov,pair,Finset.smul_sum,Finset.sum_add_distrib]
lemma strength_skew (a b:Axis):strength g A a b=-strength g A b a:= by
  unfold strength
  nth_rw 1 [pair_neg (A a) (A b),smul_neg]
  abel
variable {A} (h:smooth A)
include h
lemma strength_smooth (a b:Axis):ok (strength g A a b):= ((grad_preserves a (h b)).sub (grad_preserves b (h a))).add ((pair_smooth (h a) (h b)).const_smul g)
lemma cov_smooth (a:Axis){X:ColorField G}(hX:ok X):ok (cov g A a X):= (grad_preserves a hX).add ((pair_smooth (h a) hX).const_smul g)
private lemma swap_d (a b c:Axis):grad a (grad b (A c))=grad b (grad a (A c)):= funext fun _=> grad_comm ((h c).of_le (show (↑(2:ℕ):WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt _ _

lemma comm (a b:Axis){X:ColorField G}(hX:ok X):
    cov g A a (cov g A b X) - cov g A b (cov g A a X)=g • pair (strength g A a b) X := by
  unfold cov strength
  have H (a b:Axis):grad a (grad b X+g • pair (A b) X)=grad a (grad b X)+g • (pair (grad a (A b)) X+pair (A b) (grad a X)):= by
    rw [grad_plus a (grad_preserves b hX) (show ContDiff ℝ ∞ (g • pair (A b) X) from (pair_smooth (h b) hX).const_smul g), grad_scale a g (pair_smooth (h b) hX),grad_pair a (h b) hX]
  have HH:grad a (grad b X)=grad b (grad a X):=funext fun _=>grad_comm (hX.of_le (show (↑(2:ℕ):WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)|>.contDiffAt) _ _
  rw [H,H,HH]
  simp only [pair_add,pair_scale,pair_jac (A a) (A b) X,pair_add₁,pair_diff₁,pair_scale₁,smul_add,smul_sub]
  abel

lemma bianchi (a b c:Axis):
    cov g A a (strength g A b c)+cov g A b (strength g A c a)+cov g A c (strength g A a b)=0:= by
  unfold cov strength
  have H (a b c:Axis):grad a (grad b (A c)-grad c (A b)+g • pair (A b) (A c))=
      grad a (grad b (A c))-grad a (grad c (A b))+g • (pair (grad a (A b)) (A c)+pair (A b) (grad a (A c))):= by
    rw [grad_plus a (show ContDiff ℝ ∞ (grad b (A c)-grad c (A b)) from (grad_preserves b (h c)).sub (grad_preserves c (h b))) (show ContDiff ℝ ∞ (g • pair (A b) (A c)) from (pair_smooth (h b) (h c)).const_smul g),grad_diff a (grad_preserves b (h c)) (grad_preserves c (h b)),grad_scale a _ (pair_smooth (h b) (h c)),grad_pair a (h b) (h c)]
  rw [H,H,H]
  simp only [pair_add,pair_diff,pair_scale,smul_add,smul_sub,pair_jac (A a) (A b) (A c)]
  simp only [pair_neg (pair (A a) (A b)) (A c),pair_neg (A c) (A a),pair_minus (A b),pair_neg (grad a (A b)) (A c),pair_neg (grad b (A c)) (A a),pair_neg (grad c (A a)) (A b),smul_neg,
    swap_d h a b c,swap_d h c a b,swap_d h b c a]
  abel

end YM.RG06.Continuum
