import YM.FVA2.Landau
import YM.FormalOPE.RG10.MultiGauge.Splice

/-!
# The saddle law in the chosen real based Landau coordinates

`Landau.price` is the actual Hessian pullback from tree; on any equivariant
linear slice use exactly the same Fee with our orientation. Prove Chill in the
boson sector of BV is precisely ordinary covariance of this saddle (of its link
rows). No need postulate LPT denominators. Actual mean shift in RG10 in other
files. We do not identify the momentum theta spectrum with tree on nonphysical
coordinates (the Feynman/ghost rule has different domain).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Trans
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops TreeBasis
open Wilson Based GaussianScore MultiGauge MS.Orbit MS MS.Orbit.Cog MS.Swirl
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) {n : Side} ( hn : _root_.Even n.val)
local notation "Z" => plan G n
local notation "F" => Wilson.Field G n
local notation "Cκ" => Cone G n
local notation "Dκ" => d G (rim n)
open Green

def price : Law F:= Splice.focusWith (saddle hn) (accountBasis G n).toLinearEquiv.toLinearMap (accountBasis G n).injective
lemma price_at (x y:F): (price G hn).P x y= Orb.score (accountBasis G n x) (accountBasis G n y):= rfl
lemma quadratics (v:F): (price G hn).P v v=2*Radial.jet (WilsonPull Z) 2 v:= by
    rw [price_at,second_jet,pull_quad, exactly]; congr 1; exact (GermLaplace.jet_pull (accountBasis G n).toContinuousLinearMap _ (fiscal_smooth.contDiffAt.of_le le_top) v 2).symm
lemma measure_price : Radial.kernel (WilsonPull Z)=(price G hn).kern:= by ext x; unfold Radial.kernel Law.kern; rw [quadratics]; ring_nf

section W
-- identify metric regardless of transversal gauge, so compare Curl Hessian on full eq sector
omit hn
variable {G}
lemma colour_add (u v:Cone G n)(a:G.ColorIndex): Colour G n (u+v) a=Colour G n u a+Colour G n v a:= by ext x y; unfold Colour GColor; rw [map_add]; rfl
lemma curl_add (u v:ArrayA n) (i j:Axis) : curl (u+v) i j=curl u i j + curl v i j:= by simp only [Green.curl,Pi.add_apply,map_add]; abel
lemma curl_at (R:GaugeSlice G n) (u : Wilson.Field G n) (a:G.ColorIndex) (i j:Axis): curl (Colour G n (R.L u) a) i j=curl (Colour G n (enter G (staple n) u) a) i j:= by
   obtain ⟨p,h⟩:= where_exp G (staple n) (R.L u); rw [R.agreement] at h; rw [←h,colour_add,curl_add,grad_color, curl_grad,zero_add]
end W
local notation "M.cost" => Radial.jet
lemma pilot (R:GaugeSlice G n)(x y:F):
     (price G hn).P x y = (∑ a:G.ColorIndex, curldot (Colour G n (R.L x) a) (Colour G n (R.L y) a))/2:= by
   simp_rw [curldot,curl_at]; rw [price_at,Orb.score]; apply congr_arg (fun c:ℝ=> c/2)
   simp_rw [colour_cost]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ;
   rw [Fintype.sum_prod_type]; unfold Green.dot; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun z _=>?_; change _ * _= curl _ _ _ _*curl _ _ _ _ -- j vs z?
   have he (w:F) : letterPolar (z,j) (accountBasis G n w) i = _:= ((treeCover G n w) ▸ (curry_colour G n (enter G (staple n) w) (z,j) i)); exact congr_arg₂ (·*·) (he x) (he y)

variable (y : Site n) (j : Axis) (a : G.ColorIndex)

def xLine (y: Site n)(j : Axis)(a:G.ColorIndex): Cone G n:= fun i=> EuclideanSpace.single a (imageVLine y j i.val.2 i.val.1)
lemma x_spells (x : Site n)(i : Axis) :
    coverL G n (xLine G y j a) (x,i)=EuclideanSpace.single a (imageVLine y j i x):= by
   let U(k:Edge (Site n)):=EuclideanSpace.single a (imageVLine y j k.2 k.1); apply congr_fun ( own_image G n (x:=U) ?_) (x,i); rintro ⟨v,i⟩; unfold U; rw [show Orb.reflect (v,i)= (-v-step i,i) from rfl,imageVLine_odd]; apply PiLp.ext; intro b; by_cases he:b=a <;> simp [he]
lemma x_color (i:G.ColorIndex): Colour G n (xLine G y j a) i=if i=a then imageVLine y j else 0:= by
  by_cases h:i=a; subst i; rw [if_pos rfl]; funext b x; unfold Colour GColor; rw [x_spells]; simp
  rw [if_neg h]; funext b x; unfold Colour GColor; rw [x_spells]; simp [h]
lemma x_trans : Transverse G n (xLine G y j a):= by intro i; rw [x_color]; split; exact imageVLine_transverse ..; exact map_zero _
def xPos (y : Site n) (j : Axis) (a : G.ColorIndex) : F:= (onto G n (xLine G y j a) (x_trans G y j a)).choose
lemma x_pair : (plan G n).L (xPos G y j a)=xLine G y j a:= Exists.choose_spec (onto G n _ (x_trans G y j a))

-- `xMode` actual linear potential in lift from gauge-fixed log links

def xMode (y:Site n) (j: Axis) (a:G.ColorIndex) : Module.Dual ℝ F :=
     (EuclideanSpace.proj a).toLinearMap ∘ₗ LinearMap.proj (y,j) ∘ₗ coverL G n ∘ₗ (plan G n).L
lemma Hessian_pay (u:F): (price G hn).P (xPos G y j a) u= xMode G y j a u:= by
   rw [(price G hn).turns, pilot G hn Z,x_pair];
   rw [Finset.sum_eq_single a, x_color,if_pos rfl, Green.curldot_inverse _ (gauges G n hn u a) (fun i x=> congr_arg (fun v:G.Color=> v a) (cover_reflect G n hn ((Z).L u) (x,i)))]; rotate_left
   · intro i _ he; rw [x_color,if_neg he]; simp [Green.curldot,Green.dot, Green.curl] -- may simp
   · simp
   change (2* (xMode G y j a u))/2=_; ring
lemma x_inverse : (price G hn).inverse (xMode G y j a)=xPos G y j a:=by rw [ ← show (price G hn).P (xPos G y j a)=xMode G y j a from LinearMap.ext (Hessian_pay G hn y j a), Law.solves ]

lemma price_turn (p q:Module.Dual ℝ (Field G n)): (price G hn).wick p q=(price G hn).wick q p:=by
   let B:= price G hn; unfold Law.wick; have hp:=B.turns (B.inverse p) (B.inverse q); simp_rw [ Law.applies ] at hp; exact hp.symm

lemma image_eq (x:Site n)(i:Axis)(b:G.ColorIndex): Chill (cov G n true) (Bos i b,x) (Bos j a,y)=(((price G hn).wick (xMode G y j a) (xMode G x i b)):ℝ) := by
   let v:=xPos G y j a; have h: xMode G x i b v=(if b=a then imageVLine y j i x else 0):= by change Colour G n ((Z).L v) b i x=_; unfold v; rw [x_pair, x_color]; split <;> rfl
   unfold Law.wick; rw [ x_inverse G hn, show (xMode G x i b (xPos G y j a)) = _ from h ]; by_cases he:b=a; · subst b; rw [contracted_vector, if_pos rfl ]; rfl
   rw [cov_color _ _ he, if_neg he,Complex.ofReal_zero]
end YM.FVA2.Trans
