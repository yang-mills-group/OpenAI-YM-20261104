import YM.MS.Tone.Loud

/-!
# Curl at square as plane formula

Factor through mid-square phase; this cancels at net 0. Work at anchored root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
open Real
open Complex (I)
variable {G:Gauge}
-- `One tuple L.`
def front (x:PlaqAxes) := loadC idRail ((0:Cover),x)
def curl (x:PlaqAxes)(p: LightMode G QP)(k:Conn G): ℂ := ∑ i:Axis × Conn G, paywave p (knot (front x) i)*(curve (priv i) k:ℂ)
lemma charge2 (i:PlaqAxes) (p q: LightMode G QP): run (Sew.art (front i) gone) [p,q] = -∑ k:Conn G,curl i p k*curl i q k:= by
    unfold run Sew.art; rw [study]; let F:Cyl (Axis× Conn G) ℂ:=region.symm (ink priv gone); let s : Finset (Axis× Conn G):= Finset.univ; have hs : Uses (s:Set _) F.val:= by simp [s,Uses.entire]
    let T (p:LightMode G QP) (s:Axis×Conn G):=paywave p (knot (front i) s)
    rw [deriv_lum T p F hs]; simp_rw [deriv_lum T q (enter _ F) (s:=s) (hs.drop _), shade_nil]; simp_rw [show ∀ i j,(enter j (enter i F)).val []= _ from rank2_port (G:=G),Finset.mul_sum]; unfold curl
    -- casts
    simp_rw [Complex.ofReal_sum,Complex.ofReal_mul, Finset.sum_mul,Finset.mul_sum,mul_neg]; -- adjust
    simp_rw [Finset.sum_neg_distrib,Finset.mul_sum]; congr 1; conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr (s₁:=s) rfl; intro i _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun j _=>?_ ; unfold T; ring

-- `axis const φ positive cell`
def z (i:Axis) : QP:=(1/2:ℝ) • embed (step i)
lemma scalar (p:QP)(i:Axis): bill p (z i)= Complex.exp ((p i:ℂ)/2*I):= by
    unfold z bill pairing; rw [Finset.sum_eq_single i]; simp [emb_step]; congr 1; ring
    · intro k hk hx; simp [hx];
    simp
lemma s_wave (p:QP)(i:Axis) : bill p (z i)-bill p (- z i)= Complex.I*wave p i:= by
    rw [inverse,scalar, ← Complex.exp_neg,← neg_mul]; unfold wave theta; erw [show (p i:ℂ)/2= (((p i)/2:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,Complex.sin_neg]; dsimp only [Function.comp_apply]; rw [show (2:ℝ)⁻¹*p i=p i/2 by ring]; push_cast; ring
lemma centr (i:Axis): embed (step i)= z i+z i:= by unfold z; rw [← add_smul]; norm_num
-- test val factors separate δ color. face phase sign
-- phase factor note q of t? curl around square sign = A_i(0)-A_i(+j)+A_j(+i)-A_j(0)
def blade (x y i:Axis)(p:QP):ℝ:= (if i=y then wave p x else 0) - if i=x then wave p y else 0

def matchA (u v: Conn G)(c:ℂ):= if u=v then c else 0

def saw (x: PlaqAxes)(p:QP):= bill p (z x.val.1+ z x.val.2)
def waveForm (p: QP)(i: Axis)(c:Conn G): LightMode G QP:=((Landau.gauge i,c),p)
-- derive 4 port formula avoiding color explosion
lemma frontPiece (x:PlaqAxes) (p: LightMode G QP)(k: Conn G) : curl x p k= paywave p (knot (front x) (0,k)) + paywave p (knot (front x) (1,k))-paywave p (knot (front x) (2,k))-paywave p (knot (front x) (3,k)):=by
    unfold curl; rw [Fintype.sum_prod_type]; unfold Axis; rw [Fin.sum_univ_four]; simp only [curves,PiLp.add_apply,PiLp.sub_apply,priv]; simp [baseC,PiLp.single_apply, apply_ite]; ring
lemma please (x:Edge Cover)(a:Axis)(c t:Conn G)(p:QP): paywave (waveForm p a c) (formAt x.2 t x.1)= matchA t c (if a=x.2 then bill p (embed x.1+z x.2) else 0):= by
   unfold paywave waveForm formAt Landau.gauge way bornv
   by_cases h:a=x.2 <;> by_cases he:t=c <;> simp [matchA,h,he,eq_comm,z]; simp [Ne.symm he]
lemma curl_piece (x:PlaqAxes)(p:QP)(i:Axis)(c k:Conn G): curl x (waveForm p i c) k= matchA c k (saw x p * (I*(blade x.val.1 x.val.2 i p))):=by
    rw [frontPiece]; unfold knot; simp_rw [show ∀ u:Edge Cover,paywave (waveForm p i c) (formAt u.2 k u.1)=_ from fun u=> please u i c k p]; -- may not match framing k projection.
    by_cases he:c=k; swap; · simp [matchA,he,Ne.symm he]
    let a:=x.val.1; let b:=x.val.2;
    have ht u v : bill p (embed (0:Cover)+z u)-bill p (embed (step v)+ z u)= bill p (z u+z v)*(-(I*(wave p v))) := by
       rw [← s_wave p v]; rw [show embed 0=(0:QP) from funext fun _=>Int.cast_zero,zero_add,mul_neg,mul_sub,← rightadd,← rightadd,add_neg_cancel_right,centr]; rw [show z v + z v + z u=z u+z v+z v by abel]; ring
    unfold matchA saw; rw [he]; simp only [if_true]; have hV := x.property; unfold blade; have hB := ht x.val.2 x.val.1; rw [add_comm (z _) (z _)] at hB
    simp only [front,loadC,idRail,zero_add,Matrix.cons_val_zero,Matrix.cons_val_one,show (![(0,x.val.1), (step x.val.1,x.val.2), (step x.val.2,x.val.1), (0,x.val.2)]:Axis→Edge Cover) 2=(step x.val.2,x.val.1) from rfl,show (![(0,x.val.1),(step x.val.1,x.val.2),(step x.val.2,x.val.1),(0,x.val.2)]:Axis→Edge Cover) 3=(0,x.val.2) from rfl]; split_ifs <;> push_cast <;> first| (solve| ring)|(linear_combination (ht x.val.1 x.val.2) - hB) | (linear_combination ht x.val.1 x.val.2) | (linear_combination - hB)
end YM.MS.Tone.Frame
