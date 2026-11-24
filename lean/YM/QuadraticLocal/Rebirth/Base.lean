import YM.QuadraticLocal.Rebirth.Life
import YM.QuadraticLocal.Fk.Attire
/-!
# The chart for the true coupling also uses this *whole* model action

 Forward transform from the bare g' convention of the successor (no partial
 cubic/quartic subtraction). Compare `fromRun` prescription to these same
 coefficients in g units. Does not move any physical coupling (use
 Membership + Recharged to compare when implementing the reset physically).
 **All** Mark.Field charged to extra Term SOP; `T.Price` & L independent
 of evaluated Θ. No registering horizons by later Θ changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Faith
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Extra.Iteration
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet AllOrder.Floe AllOrder.Floe.Pace
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{n : Side}
open Comparison.RG02 Comparison.RG02.Adjacent
open QuadraticLocal.Rebirth
namespace Spirit
-- change readout convention on signed bank via THIS unit graph
local notation "Φ"=> (Stationary.Link G n)
variable (F G' U:Pace.Scene G)(K:Adjacent.UnitCost)(r i:ℕ)
set_option quotPrecheck false
local notation "f"=> K.rating
local notation "H" x:max=> ( f x )
local notation "E"=> K.enter
-- ages using real f; hold same physical A via chart → inverse on Link

def glance (k:ℕ) (F:Pace.Scene G)(K:UnitCost) (x:Stationary.Link G n)(t:ℝ):= delay (fun i=> F i n ((K.rating t)⁻¹ • x)) k (K.enter t)
def Compatible (K:UnitCost)(r:ℕ)(F G':Pace.Scene G) : Prop:=∀ (n:Side)(x:Stationary.Link G n), Act r ( Spirit.glance r F K x ) (fun i=> G' i n x)
variable {F G' U K r}
namespace Compatible
variable (A: Spirit.Compatible K r F G')
include A
lemma height (i:ℕ)(hx: i≤r)(x:Stationary.Link G n) : someJ (Spirit.glance r F K x) i = G' i n x:= (A n x).writes _ hx
variable {X:Scene G}
lemma add (hp:Spirit.Compatible K r U X): Spirit.Compatible K r (F+U) (G'+X):= fun n x=> ((A n x).add (hp n x)).realizes (Eventually.of_forall (fun y=>by simp only [glance,delay,Pi.add_apply,smul_add,sum_add_distrib])) -- equiv
omit A
lemma zero (K:UnitCost)(r:ℕ):Spirit.Compatible (G:=G) K r 0 0:=by intro n x; unfold glance delay; simp only [Pi.zero_apply,smul_zero,Finset.sum_const_zero]; exact (Act.static (0:ℝ)).repairs (fun i _=> by simp [just])
lemma sum {α:Type*}(s:Finset α){G':α→Scene G}{F':α→Scene G}(hp:∀i∈s,Spirit.Compatible K r (F' i) (G' i)): Spirit.Compatible K r (∑ i∈s,F' i) (∑ i∈s,G' i):= by
    induction s using Finset.induction with | empty=>rw [sum_empty,sum_empty]; exact zero K r| insert i s he ih=> rw [sum_insert he,sum_insert he]; exact (hp _ (mem_insert_self ..)).add (ih fun i hi=> hp _ (mem_insert_of_mem hi))
end Compatible
-- homogeneity passport
abbrev Income (F: Pace.Scene G)(j:ℤ)(k:ℕ):Prop:=∀ i≤ k,∀ (n:Side)(x:Stationary.Link G n),∀ t:ℝ,t ≠0 → t^i * F i n (t⁻¹ • x)= t^j * F i n x
open Comparison.RG02.Moving Comparison.RG02.Moving.Path Comparison.RG02.Moving.Shift

variable {s:ℤ} (ht:Income F s r) {q:Pace.Coin}(he: Act r (fun x=> K.rating x ^ s) q)
include ht he
lemma work : Spirit.Compatible K r F ( factor q F ):= by
   intro n x; let p₀:Coin:= fun i=> F i n x; have hV: Act r (delay p₀ r) p₀:= Act.swell p₀ (le_refl r); let f₀(t:ℝ):= ( f t ) ^ s; let hh:Act r ( f₀*delay p₀ r ) (Laplace.SigmaP.plus q p₀):= exact_prod he hV; apply ((hh.repairs (b:=(fun i=> factor q F i n x)) ?_ ).realizes ?_);
   · filter_upwards [K.bright] with v hv; unfold glance UnitCost.enter; unfold delay; simp only [Pi.mul_apply, smul_eq_mul, mul_sum]; apply Finset.sum_congr rfl; intro k hk; rw [mul_pow,mul_assoc (v^k),ht k (mem_range_succ_iff.mp hk) n x _ hv.ne']; unfold f₀; ring -- `mul_assoc v` expects v^...
   intro i hi; rfl
omit ht he

variable (Q:Pace.Coin)(h:Q 0=0)(L:ℕ)(R:PathData G)(p:Clip)
local notation "K₀"=> (caliber Q h).direct L
-- exact kinetic scalar exponent -2.Scale by declared full tariff. all finite.Pace uses true predictor cost.Buy.
lemma deposits : Act L (fun t=> ((K₀).rating t)^(-(2:ℤ))) ( Q + just 1 ):= by
   apply ((Act.swell ( (caliber Q h).measure ) le_rfl)).realizes -- typo; function expected `Φ`
   filter_upwards [(caliber Q h).rates L] with x hx; change delay ( Q + just 1 ) L x= _; rw [show delay ( Q + just 1 ) L x= (caliber Q h).tariff L x from rfl]; exact Eq.trans ((caliber Q h).income L x hx.le).symm (by simp; rfl) -- income name? K.income
lemma basic : Spirit.Compatible ( (caliber Q h).direct L ) L ( Pace.base p R ) ( Pace.base p R + factor Q ( Pace.base p R ) ):= by
 let b:= Pace.base p R; have hv: Spirit.Compatible ((caliber Q h).direct L) L b (factor (Q+just 1) b) := by
     refine work (s:=-(2:ℤ)) (fun i _ n x t hh=>?_) (deposits Q h L); unfold b Pace.base; let w:=mainTerm p R ∘ (Stationary.input G n); have ht : Radial.jet w (i+2) (t⁻¹ • x)=(t⁻¹)^(i+2)*Radial.jet w (i+2) x:= Tensor.homogeneous (Tensor.coeff w (i+2) 0) x t⁻¹; change t^i * Radial.jet w (i+2) (t⁻¹ • x)= t^(-(2:ℤ))* Radial.jet w (i+2) x; rw [ht,pow_add,inv_pow,inv_pow]; field_simp -- try norm_num
 have hx: factor (Q+just 1) b= b+Pace.factor Q b:= by
    funext k n; change _=(b k n)+(Pace.factor Q b k n); rw [weighs,weighs]; simp only [Pi.add_apply,add_smul, Finset.sum_add_distrib]; rw [← weighs (just 1) b,Crest.nostep,add_comm]
 rw [hx] at hv; exact hv
end Spirit
end YM.QuadraticLocal.Faith
