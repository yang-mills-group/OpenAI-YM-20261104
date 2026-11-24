import YM.Integration.WilsonOriginalMixedRadialPrice
import YM.Integration.WilsonEmittedRootedJetWage

/-! A filed group word at its suspended Laurent order. The physical thermal derivative is taken at zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSuspendedWord
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Exterior Stationary
open PertExtension.Series WilsonOriginalGroupInkDirections WilsonEmittedRootedJetWage WilsonOriginalLinkedAngularPage
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

abbrev Split (G:Gauge) (n:Side):=ℝ×Link G n

def raw (T:Row o J G X) (extra:ℕ) (z:Split G n):ℝ:=
  z.1^(extra+T.lamp.stamp)*Helmet.frame T.atom T.center z.2

def colored (T:Row o J G X) (t:X) (extra:ℕ) (z:Joint G n):ℂ:=
  T.paint t*(z.1^extra*Loan.letter T.lamp T.atom T.center z.1 (RG.increment 1 z.2):ℝ)

def split (G:Gauge) (n:Side) : Joint G n→L[ℝ]Split G n :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (edgeColor.symm.toContinuousLinearMap)

def spoke (G:Gauge) (n:Side) : Slot G n→Split G n
  | none => (1,0)
  | some a => (0,ray G a)

theorem read (T:Row o J G X) (extra:ℕ) (m:ℕ) (z:Split G n) :
    Radial.jet (raw T extra) m z=
      if extra+T.lamp.stamp≤ m then z.1^(extra+T.lamp.stamp)*
        Radial.jet (Helmet.frame T.atom T.center) (m-(extra+T.lamp.stamp)) z.2 else 0 :=
  AllOrder.Floe.favor_exp _ (Helmet.frameGrade T.atom T.center).smooth z.1 z.2 m _

theorem original (T:Row o J G X) (t:X) (extra:ℕ) :
    colored T t extra=(fun z:Split G n=>T.paint t*(raw T extra z:ℝ)) ∘ split G n := by
  funext z
  have field:Stationary.input G n (edgeColor.symm z.2)=RG.increment 1 z.2:=by
    funext e
    rw [input_color,ContinuousLinearEquiv.apply_symm_apply]
    change _=G.lieExp (z.2 e)*1
    rw [mul_one]
  change T.paint t*((z.1^extra*(z.1^T.lamp.stamp*T.atom.unmasked (RG.increment 1 z.2) T.center)):ℝ)=
    T.paint t*((z.1^(extra+T.lamp.stamp)*T.atom.unmasked (Stationary.input G n (edgeColor.symm z.2)) T.center):ℝ)
  rw [field,pow_add,mul_assoc]

def price (G:Gauge) (σ:ℝ) (m:ℕ) : ℝ :=
  WilsonMarkedAngularTestInvoice.fee m m * (max 1 (m:ℝ))^m *
    (max 1 (2*(G.colorScale*(weight G*m))/σ))^m

theorem nonnegative {σ:ℝ} (m:ℕ):0≤price G σ m:=by
  unfold price
  exact mul_nonneg (mul_nonneg (WilsonMarkedAngularTestInvoice.fee_nonnegative m m) (by positivity)) (by positivity)

theorem smooth (T:Row o J G X) (extra:ℕ) : ContDiffAt ℝ ω (raw T extra) 0 := by
  have h:ContDiffAt ℝ ω (Helmet.frame T.atom T.center) (0:Link G n):=(Helmet.frameGrade T.atom T.center).smooth
  exact (contDiffAt_fst.pow _).mul (h.comp (f:=Prod.snd) (0:Split G n) contDiffAt_snd)

theorem paid (T:Row o J G X) (t:X) (extra m:ℕ) (u:Fin m→Slot G n) {σ:ℝ}
    (hs:0<σ) (deposit:T.Budget) (growth:T.Graceful σ):
    ‖iteratedFDeriv ℝ m (colored T t extra) 0 (peg G n ∘ u)‖ ≤ T.salary*price G σ m:=by
  let b:=(max 1 (m:ℝ))^m
  let c:=weight G*m
  let a:=(max 1 (2*(G.colorScale*c)/σ))^m
  have a0:0≤a:=by unfold a;positivity
  have b0:0≤b:=by unfold b;positivity
  have c0:0≤c:=mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  have bound (z:Split G n) (small:‖z‖≤(m:ℝ)):
      |‖T.paint t‖*Radial.jet (raw T extra) m z|≤T.salary*(b*a):=by
    rw [read];split
    · rename_i he
      have haxis (e:Edge (Site n)):‖collect G (arm G n 1 z.2) e‖≤c:=
        (WilsonOriginalGroupInkDirections.axis z.2 e).trans
          (mul_le_mul_of_nonneg_left ((norm_snd_le z).trans small) (norm_nonneg _))
      have coeff:=WilsonReceivedSourceCoefficientBound.radial T t z.2 hs c0 haxis deposit growth
        (m-(extra+T.lamp.stamp))
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at coeff
      have coef:2*(G.colorScale*c)/σ≥0:=div_nonneg (mul_nonneg (by norm_num) (mul_nonneg G.colorScale_pos.le c0)) hs.le
      have hb:|z.1|^(extra+T.lamp.stamp)≤b:=
        (pow_le_pow_left₀ (abs_nonneg _) (((norm_fst_le z).trans small).trans (le_max_right 1 _)) _).trans
        (pow_le_pow_right₀ (le_max_left 1 _) he)
      have ha:(2*(G.colorScale*c)/σ)^(m-(extra+T.lamp.stamp))≤a:=
        (pow_le_pow_left₀ coef (le_max_right 1 _) _).trans (pow_le_pow_right₀ (le_max_left 1 _) (Nat.sub_le ..))
      rw [abs_mul,abs_mul,abs_pow,abs_of_nonneg (norm_nonneg _)]
      calc
        _=|z.1|^(extra+T.lamp.stamp)*(‖T.paint t‖*|Radial.jet (Helmet.frame T.atom T.center) _ z.2|):=by ring
        _≤b*(T.salary*a):=mul_le_mul hb (coeff.trans (mul_le_mul_of_nonneg_left ha T.sound.le))
          (mul_nonneg (norm_nonneg _) (abs_nonneg _)) b0
        _=_:=by ring
    · simpa using mul_nonneg T.sound.le (mul_nonneg b0 a0)
  let F:Split G n→ℂ:=fun z=>T.paint t*(raw T extra z:ℝ)
  have fit:ContDiffAt ℝ m F 0:=by
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 ((smooth T extra).of_le le_top))
  have atPeg (s:Slot G n):split G n (peg G n s)=spoke G n s:=by
    cases s with
    | none =>
      apply Prod.ext
      · rfl
      · change edgeColor.symm (0:Directions G n)=0
        exact edgeColor.symm.map_zero
    | some y =>
      apply Prod.ext
      · rfl
      · exact edgeColor.symm_apply_apply _
  have units (i:Fin m):‖spoke G n (u i)‖≤1:=by
    cases e:u i with
    | none=>change max ‖(1:ℝ)‖ ‖(0:Link G n)‖≤1;simp
    | some y=>
      change max ‖(0:ℝ)‖ ‖ray G y‖≤1
      apply max_le (by norm_num)
      apply (pi_norm_le_iff_of_nonneg (by norm_num:0≤(1:ℝ))).mpr
      intro x;change ‖if x=y then (1:ℝ) else 0‖≤1;split <;> norm_num
  rw [original,Next.Foundations.jets_linear (split G n) fit,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have move:(fun j=>split G n ((peg G n ∘ u) j))=fun j=>spoke G n (u j):=funext fun j=>atPeg (u j)
  rw [move]
  exact (WilsonOriginalMixedRadialPrice.original (raw T extra) (T.paint t) m (smooth T extra)
    (mul_nonneg T.sound.le (mul_nonneg b0 a0)) bound _ units).trans_eq (by unfold price;change _=T.salary*((_*b)*a);ring)

end YM.Integration.WilsonOriginalSuspendedWord
