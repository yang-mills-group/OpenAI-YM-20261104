import YM.RegulatorIR.Ward.Churn
import YM.RegulatorIR.Tape.Hound

/-!
# Finite-regulator gauge eddy evaluated along smooth rescaled curves
Applies to all unsoftened orbit steps, no uniform Taylor. Need another Ward
statement for the unfolded vacuum jets to permit alignment at positive order. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Ward
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Matrix
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I:Type} [Fintype I]{G: Gauge}{n:Side}{K:Matrix (Book G n) (Book G n) ℝ}
variable {g:ℝ→ℝ}{s m e:ℕ} {T U: Orders (Book G n)}
variable {x y : ℝ → Horizon G n}

def reel_prop (x y:ℝ→ Horizon G n):Prop := ∀ᶠ t in 𝓝 0,∃ k: Site n→ G.El, compatible k ∧ climb (t • x t)= goat k (climb (t • y t))

abbrev peel (x:ℝ→ Horizon G n): ℝ → Book G n→ℝ := fun t=>paper G n (x t)
-- substitution on t-rescaled fields

def reel (T:Orders (Book G n)) (m:ℕ) (x:ℝ→Horizon G n):= ocean (churn (peel x)) (rated (fun i=> i+m) T)

def steam (K: Matrix (Book G n) (Book G n) ℝ) : Horizon G n→ℝ:= fun w=> -(beneath K w)
def money (K: Matrix (Book G n) (Book G n) ℝ) (T: Orders (Book G n)) (x:ℝ→Horizon G n):=tale (steam K ∘ x)+reel T 2 x
lemma reel_cost (F:ℝ→ ℝ)(h:ContDiffAt ℝ ∞ F 0) : tale (fun t=>Real.exp (F t))= PowerSeries.C (Real.exp (F 0))*expo (tale F-PowerSeries.C (F 0)) := by
 let C:=F 0; let f:= fun t=> F t-C
 let k:=(fun _:ℝ=>C); have hp: ContDiffAt ℝ ∞ f 0 := h.sub contDiffAt_const
 have ht: tale f = tale F-PowerSeries.C C:= by rw [show f=F + -k from Eq.symm (sub_eq_add_neg ..), tale_add (g:=-k) h (show ContDiffAt ℝ ∞ (-k) 0 from (show ContDiffAt ℝ ∞ k 0 from contDiffAt_const).neg),tale_neg (f:=k) contDiffAt_const,tale_const]; exact Eq.symm (sub_eq_add_neg ..)
 rw [show (fun t=>Real.exp (F t))=(fun _=>Real.exp C)*(fun t=>Real.exp (f t)) from funext (fun t=> by rw [Pi.mul_apply];rw [← Real.exp_add,show C+f t=F t by unfold f;abel]), tale_mul (g:=fun t=>Real.exp (f t)) contDiffAt_const hp.exp,tale_const, tale_ex (f:=f) (sub_self _) hp, ht]

lemma reel_dark {m:ℕ}(T:Orders (Book G n)) (h:Vacuum T) : coeff 0 (rated (fun i=>i+m) T)=0:= by rw [rated_v,vacuum_lo T h]; simp [packed]
lemma steam_smooth (K:Matrix (Book G n) (Book G n) ℝ): ContDiff ℝ ∞ (steam K):=by
 unfold steam beneath phase dotProduct mulVec dotProduct;have hv : ContDiff ℝ ∞ (paper G n):=(paper G n).toLinearMap.toContinuousLinearMap.contDiff; fun_prop
omit [Fintype I] in
lemma evaluation (p:I→ℝ) : (emphasis p).toRingHom= MvPolynomial.eval p:= RingHom.ext fun _=>language ..
omit [Fintype I] in
lemma rescaling (p : I→ℝ)(τ:ℝ⟦X⟧) : PowerSeries.map (emphasis p).toRingHom (PowerSeries.map (algebraMap ℝ (Jet I)) τ)=τ:=by
 ext1 i; rw [coeff_map,coeff_map];exact (emphasis p).commutes _

namespace RangeR
variable (R: RangeR G n (beneath K) g s m T U)

def cyclone (x:ℝ→Horizon G n) := tale (fun t=>Real.exp ((steam K) (x t)))*R.scalar * expo (reel T 2 x)

abbrev spinD (R:RangeR G n (beneath K) g s m T U) : PowerSeries (Jet (Book G n)):= PowerSeries.map (algebraMap ℝ (Jet (Book G n))) R.scalar* expo (rated (fun i=>i+2) T)
abbrev mav (x:Horizon G n):=Real.exp (steam K x)

lemma binds (w:Horizon G n): manuscript R.Val 1 w=PowerSeries.C (mav (K:=K) w)*PowerSeries.map (MvPolynomial.eval (paper G n w)) (spinD R):= by
 let p:= paper G n w
 rw [R.marks.bare w,← evaluation,spinD,map_mul,rescaling, Formal.map_exp]; unfold flavor;rw [mul_assoc];rfl
lemma winds (x:ℝ→ Horizon G n): cyclone R x=tale (fun t=> mav (K:=K) (x t))* ocean (churn (peel x)) (spinD R):=by unfold cyclone spinD reel; rw [map_mul,ocean_const,solar _ _ (reel_dark T R.marks.vacuum),mul_assoc]
lemma lifts {x:ℝ→ Horizon G n} (h:ContDiffAt ℝ ∞ x 0) : Lift (peel x):= fun i=> (contDiff_apply ℝ ℝ i).contDiffAt.comp _ ((paper G n).toLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp _ h)
lemma threaded {y:ℝ→Horizon G n}(h:ContDiffAt ℝ ∞ y 0) : Script (cyclone R y) fun t=>normalized R.Val 1 t (y t):=by
 rw [winds]; refine prolong _ _ (R.basis.allows shapeOne).beats (fun w=>mav w (K:=K)) (paper G n) _ (binds R) y h.continuousAt (((steam_smooth _).contDiffAt.comp _ h).exp) (lifts h)
lemma summoned {y:ℝ→ Horizon G n}(h:ContDiffAt ℝ ∞ y 0) : Script ((cyclone R y)*(X^s)*reel U m y) fun t=>normalized R.Val R.Mark t (y t):= by
 let P:=(spinD R)*(X^s)*rated (fun i=> i+m) U
 have Hx(w:Horizon G n) : manuscript R.Val R.Mark w=PowerSeries.C (mav w (K:=K))*PowerSeries.map (MvPolynomial.eval (paper G n w)) P:=by
    rw [R.marks.stamped,binds R,← evaluation]; unfold P spinD flavor; simp only [map_mul,map_pow,PowerSeries.map_X]; simp_rw [mul_assoc];rfl
 rw [winds R y]; let χ:=tale (fun t=> mav (y t) (K:=K)); have hp: (χ * ocean (churn (peel y)) (spinD R))*X^s * reel U m y= χ * ocean (churn (peel y)) P:=by unfold P reel spinD; simp only [map_mul,map_pow,show ocean (churn (peel y)) PowerSeries.X=PowerSeries.X from tide_X ..]; ring
 change Script ((χ * _) * PowerSeries.X^s * reel U m y) _; rw [hp]; exact prolong _ _ (R.basis.allows R.inscription).beats _ (fun w=>paper G n w) _ Hx y h.continuousAt (((steam_smooth _).contDiffAt.comp _ h).exp) (lifts h)

private lemma equal_letters (r:reel_prop x y) (F A: Hook G I (OEdge n))(h:Archive G n F A): (fun t=> normalized F A t (x t))=ᶠ[Tested.germ] (fun t=> normalized F A t (y t)) := by
 filter_upwards [r.filter_mono nhdsWithin_le_nhds] with j hj; obtain ⟨k,hk,hh⟩:=hj;unfold normalized;rw [show Chart.expLinks _ _ _ = _ from hh,h k hk (climb (j • y j))]

include R
variable (H:ContDiffAt ℝ ∞ x 0) (Ht:ContDiffAt ℝ ∞ y 0) (hr : reel_prop x y)
include H Ht hr
lemma orbit_eq : cyclone R x=cyclone R y:=by
 ext1 i; refine congr_fun (Aspiration.unique (Script.bend (threaded R H) (equal_letters hr _ _ R.archive1)) (threaded R Ht)) i
omit H Ht hr in
lemma cyclone_base : coeff 0 (cyclone R x)= Real.exp (steam K (x 0))*coeff 0 R.scalar:=by
 rw [cyclone]; let f(w:Horizon G n):= Real.exp (steam K w); simp_rw [coeff_zero_eq_constantCoeff_apply,map_mul]; rw [← coeff_zero_eq_constantCoeff_apply,← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,tale_base, exp_start]; simp
-- Both marked equality and vacuum normalized difference, no scalar divided on degenerate Gram. Cancellation independent of number of softening kernels.
lemma stamps : reel U m x=reel U m y:=by
 have hx: (cyclone R x)*X^s*reel U m x=(cyclone R y)*X^s* reel U m y:=by ext1 i; exact congr_fun (Aspiration.unique (Script.bend (summoned R H) (equal_letters hr _ _ R.archive2)) (summoned R Ht)) i
 rw [← orbit_eq R H Ht hr] at hx; apply mul_left_cancel₀ _ hx
 apply mul_ne_zero _ (pow_ne_zero _ X_ne_zero); intro h;have hh:=cyclone_base R (x:=x); rw [h, map_zero] at hh; exact (lt_irrefl 0) (lt_of_lt_of_le (mul_pos (Real.exp_pos _) R.marks.awake) hh.ge)
omit hr in
lemma money_unique (Hx:cyclone R x=cyclone R y) : money K T x=money K T y:=by
 have hp:(steam K) (x 0)=(steam K) (y 0):=by
    apply Real.exp_injective;apply mul_right_cancel₀ (R.marks.awake.ne'); rw [← cyclone_base R,Hx,cyclone_base R]
 let d:=steam K (x 0); let t:=PowerSeries.C d
 have he {x:ℝ→Horizon G n}(h:ContDiffAt ℝ ∞ x 0) (hx:steam K (x 0)=d) : (coeff 0 (money K T x-t)=0) ∧ cyclone R x= (PowerSeries.C (Real.exp d)*R.scalar)*expo (money K T x-t):=by
    let F:=steam K ∘ x; let A:=tale F; let B:=reel T 2 x
    have hD : F 0=d:=hx;have hb : coeff 0 B=0:= by unfold B reel; rw [submerge]; simp [reel_dark T R.marks.vacuum]
    have ha: coeff 0 (A-t)=0:=by unfold A t; rw [map_sub, tale_base,coeff_zero_C,hD,sub_self]
    rw [show money K T x-t=(A-t)+B by unfold money A B F;abel]; refine ⟨by rw [map_add,ha,hb,add_zero],?_⟩
    unfold cyclone; change tale (fun t=>Real.exp (F t))*R.scalar*expo B= _; rw [timble_exp ha hb,reel_cost F ((steam_smooth K).contDiffAt.comp _ h), hD]; change PowerSeries.C (Real.exp d)*expo (A-t)* R.scalar * _=_; ring
 have hx:= he H rfl; have hy:= he Ht hp.symm
 suffices hf :money K T x - t=money K T y - t from sub_left_inj.mp hf
 ext1 i
 apply Squares.script_inject hx.1 hy.1 (e:=i) _ _ le_rfl
 apply Squares.left (f:= PowerSeries.C (Real.exp d)*R.scalar) (by rw [coeff_C_mul]; exact mul_ne_zero (Real.exp_pos _).ne' R.marks.awake.ne')
 rw [← hx.2,← hy.2,Hx]; exact fun _ _=> rfl
lemma norms : money K T x=money K T y:= money_unique R H Ht (orbit_eq R H Ht hr)
end RangeR
end YM.RegulatorIR.Ward
