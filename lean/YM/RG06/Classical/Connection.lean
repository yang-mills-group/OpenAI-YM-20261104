import YM.Maxwell.Exterior
import YM.Gauge.Casimir
import YM.Push.LOOP_COEFFICIENT.Color
/-!
# Off-shell independent operator language (before extensions/contact mixing)

No group or graph measure. Lie generators are the real physical-color linear
coordinates of `Gauge.colorMat`, i.e. -Re tr(XY)/repDim, not ad-normalized.
Gauge coupling `g` is displayed separately; spatial holonomies in
`Source` use g=1. `word` uses derivative values (not Taylor coefficients) in
listed order **outermost FIRST**, including all tensor components. No equations
or divergence conditions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Connection
open Analysis Function Filter Set
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators
variable {G : Gauge}

abbrev Field (G:Gauge) := Axis → E4 → G.Color

/-- connection as one form evaluated at constant direction v -/
def leg (A:Field G) (v:E4)(x:E4):G.Color:=∑ i:Axis,v i • A i x

abbrev Regular (A:Field G)(x:E4):Prop:=∀ i, ContDiffAt ℝ ∞ (A i) x

def shift (g:ℝ)(A:Field G)(i:E4)(p:E4→G.Color)(x:E4):G.Color:=D i p x+ g • G.ad (leg A i x) (p x)

def twist (g:ℝ)(A:Field G)(i j:E4)(x:E4):G.Color:=D i (leg A j) x-D j (leg A i) x + g • G.ad (leg A i x) (leg A j x)

def word (g:ℝ)(A:Field G) : List E4 → E4 → E4 → E4 → G.Color
 | [],i,j=> twist g A i j
 | k::l,i,j=>shift g A k (word g A l i j)

structure Address where
    letters : List Axis
    first : Axis
    second : Axis
  deriving DecidableEq

namespace Address
def read (s:Address)(g:ℝ)(A:Field G):= word g A (s.letters.map basis) (basis s.first) (basis s.second)
def degree (s:Address):=s.letters.length+2
end Address

/-- reuse finite-dim conversion of Push.Loops. -/
def Lie (G:Gauge) := (LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad).toContinuousLinearMap
@[simp] lemma Lie_apply (x y:G.Color): Lie G x y=G.ad x y:=rfl

lemma ad_sym (x y:G.Color): G.ad x y = -G.ad y x:= Push.Loops.ad_flip x y
lemma ad_nil (x:G.Color): G.ad x x=0:= by
  apply G.colorMat_injective; simp
lemma ad_color (a:G.El)(x y:G.Color):G.ad (G.adjoint a x) (G.adjoint a y)=G.adjoint a (G.ad x y):=by
  apply G.colorMat_injective
  rw [G.colorMat_ad,G.mat_adjoint,G.mat_adjoint,G.mat_adjoint,G.colorMat_ad]
  let b:=G.mat a
  unfold Gauge.conjugate
  have h:star b*b=1:= by rw [← G.mat_inv,← G.mat_mul,inv_mul_cancel,G.mat_one]
  rw [mul_sub,sub_mul]
  have hx (X Y:G.Mat): b * X * star b * (b * Y * star b)=b*(X*Y)*star b:=by calc
    _=b * X * (star b * b) * Y * star b:=by rw [mul_assoc]; simp only [mul_assoc]
    _=_:=by rw [h,mul_one]; simp only [mul_assoc]
  change b * G.colorMat x * star b * (b * G.colorMat y * star b) - (b * G.colorMat y * star b * (b * G.colorMat x * star b)) = b * (G.colorMat x * G.colorMat y) * star b - b * (G.colorMat y * G.colorMat x) * star b
  rw [hx,hx]

@[simp] lemma leg_basis (A:Field G)(i:Axis): leg A (basis i)= A i := by
  funext x
  simp [leg,ite_smul]

lemma leg_reg (A:Field G)(v:E4){x:E4}(h:Regular A x):ContDiffAt ℝ ∞ (leg A v) x:=
  ContDiffAt.sum fun i _=>(h i).const_smul _

section rates
variable {E F H Y : Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup H][NormedAddCommGroup Y]
  [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ H][NormedSpace ℝ Y]{x:E}
  {f:E→F}{h:E→H}

lemma smooth_D {v:E}(h:ContDiffAt ℝ ∞ f x):ContDiffAt ℝ ∞ (D v f) x:=dSmooth h v (by simp)

lemma smooth_bilin (m:WithTop ℕ∞)(L:F→L[ℝ]H→L[ℝ]Y)(hf:ContDiffAt ℝ m f x)(hh:ContDiffAt ℝ m h x):
    ContDiffAt ℝ m (fun y=>L (f y) (h y)) x:= (L.contDiff.contDiffAt.comp x hf).clm_apply hh

lemma rate_bilin (L:F→L[ℝ]H→L[ℝ]Y)(hf:DifferentiableAt ℝ f x)(hh:DifferentiableAt ℝ h x)(v:E):
    D v (fun y=>L (f y) (h y)) x=L (D v f x) (h x) + L (f x) (D v h x):=by
  have hi := (L.hasFDerivAt.comp x hf.hasFDerivAt).clm_apply hh.hasFDerivAt
  unfold D
  simp only [Function.comp_def] at hi
  rw [hi.fderiv,add_comm]; rfl

lemma rate_add {q:E→F}(v:E)(he:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ q x):
    D v (fun y=> f y + q y) x = D v f x + D v q x:=by
  change fderiv ℝ (f+q) x v=_; rw [fderiv_add he hg]; rfl
lemma rate_sub {q:E→F}(v:E)(he:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ q x):
    D v (fun y=> f y - q y) x = D v f x - D v q x:=by
  change fderiv ℝ (f-q) x v=_; rw [fderiv_sub he hg]; rfl
lemma rate_scale (v:E)(t:ℝ)(he:DifferentiableAt ℝ f x):
    D v (fun y=> t • f y) x=t • D v f x :=by unfold D; rw [fderiv_fun_const_smul he]; rfl
lemma rate_sum {ι:Type*} (U:Finset ι)(p:ι→E→F)(v:E)(he:∀ i∈U,DifferentiableAt ℝ (p i) x):
    D v (fun y=>∑ i∈U,p i y) x=∑ i∈U,D v (p i) x:=by
  unfold D
  rw [(HasFDerivAt.fun_sum (u:=U) fun i hi=>(he i hi).hasFDerivAt).fderiv]; exact sum_apply ..
lemma rate_map (L:F→L[ℝ]H)(v:E)(he:DifferentiableAt ℝ f x):
    D v (fun y=>L (f y)) x=L (D v f x):=by
  change fderiv ℝ ((⇑L) ∘ f) x v=_; rw [(L.hasFDerivAt.comp x he.hasFDerivAt).fderiv]; rfl
lemma rate_mul {M:Type*}[NormedRing M][NormedAlgebra ℝ M]{f h:E→M}(v:E)(he:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ h x):
    D v (fun y=> f y * h y) x = D v f x * h x + f x * D v h x:=
  rate_bilin (ContinuousLinearMap.mul ℝ M) he hg v
end rates

section forms
variable (g:ℝ)(A:Field G)
lemma shift_smooth {p:E4→G.Color}{i x:E4}(h: Regular A x)(u:ContDiffAt ℝ ∞ p x):
    ContDiffAt ℝ ∞ (shift g A i p) x := (smooth_D u).add ((smooth_bilin ∞ (Lie G) (leg_reg A _ h) u).const_smul g)
lemma twist_smooth {i j x:E4}(h:Regular A x):ContDiffAt ℝ ∞ (twist g A i j) x:= by
  exact ((smooth_D (leg_reg A _ h)).sub (smooth_D (leg_reg A _ h))).add ((smooth_bilin ∞ (Lie G) (leg_reg A _ h) (leg_reg A _ h)).const_smul g)
lemma word_smooth (s:List E4){i j x:E4}(h:Regular A x):ContDiffAt ℝ ∞ (word g A s i j) x := by
  induction s with
  | nil=>exact twist_smooth g A h
  | cons k l ih=> exact shift_smooth g A h ih

lemma shift_add (i:E4){f h:E4→G.Color}{x:E4}(he:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ h x):
    shift g A i (fun y=> f y+h y) x=shift g A i f x+shift g A i h x:=by simp_rw [shift,rate_add _ he hg,map_add,smul_add]; abel
lemma shift_scale (i:E4)(t:ℝ){f:E4→G.Color}{x:E4}(he:DifferentiableAt ℝ f x):
    shift g A i (fun y=> t • f y) x=t • shift g A i f x:=by simp_rw [shift,rate_scale i t he,map_smul,smul_add, smul_comm g t]

lemma flip_twist (i j x:E4):twist g A i j x = -twist g A j i x:=by
  simp only [twist,neg_add,neg_sub,← smul_neg]
  rw [ad_sym (leg A j x)]; simp
lemma flip_word (s:List E4)(i j:E4):word g A s i j=-word g A s j i:=by
  induction s with
  | nil=> exact funext (flip_twist g A i j)
  | cons k l ih=>
    funext x; simp only [word,ih,shift,D,fderiv_neg]
    simp only [Pi.neg_apply,map_neg,smul_neg,shift,D,neg_add,neg_apply]

/-- Ricci commutator. No equation on the connection. -/
lemma ricci (a b x:E4)(p:E4→G.Color)(he:Regular A x)(hp:ContDiffAt ℝ ∞ p x):
    shift g A a (shift g A b p) x - shift g A b (shift g A a p) x=g • G.ad (twist g A a b x) (p x):=by
  let L:=Lie G
  have hq (k:E4):= leg_reg A k he
  have hd:=hp.differentiableAt (by simp)
  have hw (a b:E4):
      shift g A a (shift g A b p) x=
      D a (D b p) x + g • (G.ad (D a (leg A b) x) (p x)+G.ad (leg A b x) (D a p x)) +
      g • (G.ad (leg A a x) (D b p x) + g • G.ad (leg A a x) (G.ad (leg A b x) (p x))):=by
    let q(y:E4):= L (leg A b y) (p y)
    have hh : ContDiffAt ℝ ∞ q x := smooth_bilin ∞ L (hq b) hp
    have hv:=hh.differentiableAt (by simp)
    unfold shift
    change D a (fun y=>D b p y+ g • q y) x + g • G.ad (leg A a x) (D b p x + g • G.ad _ _) = _
    rw [rate_add a ((smooth_D hp).differentiableAt (by simp)) ((hh.const_smul g).differentiableAt (by simp)), rate_scale _ _ hv,map_add,map_smul]; unfold q
    rw [rate_bilin L ((hq b).differentiableAt (by simp)) hd]
    rfl
  have hj (p q r:G.Color): G.ad p (G.ad q r)-G.ad q (G.ad p r)=G.ad (G.ad p q) r:=by
    apply G.colorMat_injective
    simp only [map_sub,G.colorMat_ad]; noncomm_ring
  rw [hw a b,hw b a,twist,commuteD (hp.of_le (show (↑(2:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) a b]
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,← hj, smul_add,smul_sub]
  abel

lemma bianchi (a b c x:E4)(h:Regular A x):
    shift g A a (twist g A b c) x+shift g A b (twist g A c a) x+shift g A c (twist g A a b) x=0:=by
  have hd (a:E4):=leg_reg A a h
  have ht (a b c:E4):shift g A a (twist g A b c) x=D a (D b (leg A c)) x-D a (D c (leg A b)) x+
      g • (G.ad (D a (leg A b) x) (leg A c x)-G.ad (D a (leg A c) x) (leg A b x))+
      (g • (-G.ad (D b (leg A c) x) (leg A a x)) - g • (-G.ad (D c (leg A b) x) (leg A a x)))+
      g • g • G.ad (leg A a x) (G.ad (leg A b x) (leg A c x)):=by
    let L:=Lie G
    let p(u:E4):= L (leg A b u) (leg A c u)
    have hw:=((smooth_bilin ∞ L (hd b) (hd c)):ContDiffAt ℝ ∞ p x).differentiableAt (by simp)
    have hf (i k:E4): DifferentiableAt ℝ (D i (leg A k)) x:=(smooth_D (hd k)).differentiableAt (by simp)
    change D a (fun y=>D b (leg A c) y-D c (leg A b) y+g • p y) x+g • G.ad _ (twist g A b c x)=_
    have hv1:DifferentiableAt ℝ (fun y=>D b (leg A c) y-D c (leg A b) y) x := (hf b c).sub (hf c b)
    have hv2:DifferentiableAt ℝ (fun y:E4=>g • p y) x := ((smooth_bilin ∞ L (hd b) (hd c)).const_smul g).differentiableAt (by simp)
    rw [rate_add a hv1 hv2,rate_sub a (hf b c) (hf c b),rate_scale a g (show DifferentiableAt ℝ p x from hw),twist,map_add,map_sub,map_smul,smul_add,smul_sub]; unfold p
    rw [rate_bilin L ((hd b).differentiableAt (by simp)) ((hd c).differentiableAt (by simp))]; unfold L; rw [Lie_apply,Lie_apply]
    rw [ad_sym (leg A b x) (D a _ x), ← sub_eq_add_neg, ad_sym (leg A a x) (D b _ x),ad_sym (leg A a x) (D c _ x)]
    abel
  have hj (u v w:G.Color): G.ad u (G.ad v w)+G.ad v (G.ad w u)+G.ad w (G.ad u v)=0:=by
    apply G.colorMat_injective
    simp only [map_add,map_zero,G.colorMat_ad]; noncomm_ring
  rw [ht a b c,ht b c a,ht c a b,commuteD ((hd c).of_le (show (↑(2:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) a b,commuteD ((hd b).of_le (show (↑(2:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) a c,commuteD ((hd a).of_le (show (↑(2:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) b c]
  trans g • g • (G.ad (leg A a x) (G.ad (leg A b x) (leg A c x))+G.ad (leg A b x) (G.ad (leg A c x) (leg A a x))+G.ad (leg A c x) (G.ad (leg A a x) (leg A b x)))
  · simp only [smul_sub,smul_neg,smul_add]; abel
  rw [hj,smul_zero,smul_zero]
end forms
end YM.RG06.Connection
