import YM.FormalBulk08.Spigot.Ginza
import YM.FormalBulk08.Spigot.Road
import YM.AnalyticNext.CUBIC_MATCH.Terms.Slots
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Lines

/-!
Explicit rooted curvature packet representation, address stays centered.
Atom height/walk on the lift; no signed scalar averaging.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

lemma pigment (T:Tile (edgeL G) r)(h:Lust T)(w:chain Stoop r)(a:G.El)(x:Fin r→G.Color): (∑ i:chain (hue G) r,(T (arctic G r (w,i)))*∏ j,G.adjoint a (x j) (i j)) = (∑ i,T (arctic G r (w,i)) * ∏ j,x j (i j)):= by
    have he j (b : hue G): G.adjoint a (x j) b= ∑ i,suit a b i * x j i:= (congr_fun (shy a (x j)) b).symm
    simp_rw [he,Fintype.prod_sum,Finset.prod_mul_distrib,Finset.mul_sum,←mul_assoc]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_; rw [←Finset.sum_mul]; congr 1; exact (h a (arctic G r (w,i))).symm

def spring (a:Atom G r)(x:Link G n):= a.unmasked (input G n x) (0:Site n)
lemma spike (a:Atom G r): ContDiffAt ℝ ω (spring a (n:=n)) 0:= by
    let f := Work.F02.atomExt a (0:Site n) ∘ Work.F02.physical ∘ input G n
    have hv : ContDiffAt ℝ ω (Work.F02.physical ∘ input G n) 0:= Work.F02.physical_contDiffAt (fun j=> ?_)
    · rw [show spring a (n:=n)=Complex.reCLM ∘ f from funext fun x=>by simp [spring,f,Work.F02.atomExt_physical]]; exact Complex.reCLM.contDiff.contDiffAt.comp _ (((Work.F02.atomExt_contDiff _ _).restrict_scalars ℝ).contDiffAt.comp _ hv)
    unfold input; exact ((represent_smooth _).comp (Stationary.arm _ _ _).toContinuousLinearMap.contDiff).contDiffAt
lemma routeSpring (a:Atom G r)(x:Link G n)(j:ℕ): traceP x (PowerSeries.coeff j (paste (spring a)))= CubicMatch.term j (fun t=> a.unmasked (represent (t • Stationary.arm G n 1 x)) 0):= by
    rw [trace_paste,PertExtension.Series.Radial.homogeneous_derivative (spring a) _ _ ((spike a).of_le le_top)]
    unfold spring input CubicMatch.term; simp only [map_smul,smul_eq_mul]
lemma springPin (a:Atom G r)(x:Link G n): traceP x (PowerSeries.coeff r (paste (spring a)))=a.poly fun i=> faceCurl (slotFace (a.leg i) 0) (Stationary.arm _ _ _ x):= by rw [routeSpring]; exact (CubicMatch.slot_first a 0 (Stationary.arm G n 1 x)).1
lemma springLow (a:Atom G r)(n:Side)(j:ℕ)(h:j<r): PowerSeries.coeff j (paste (spring a (n:=n)))=0:= by apply orbit_ext; intro x; rw [show traceP x 0=0 by simp [traceP],routeSpring]; exact (CubicMatch.slot_first a 0 (Stationary.arm _ _ _ x)).2 j h

def stroke (U:Link G n)(b:hue G)(p : Edge Cover) := U (wrap n p.1,coord p.2,b)
lemma strokePin (x:Cover)(a: PlaqAxes)(b:hue G)(U: Link G n) : faceCurl (wrap n x,a) (Stationary.arm _ _ _ U) b=curlP (x,a) (stroke U b):= by
    rw [faceCurl,← Exterior.fundamental, YM.AnalyticBridge.VerifiedReset.Square.cochain_square]; unfold curlP beadCurl stroke
    simp only [map_add, wrap_step, PiLp.sub_apply]; change (_-_)-(_-_) = U _+U _-U _-U _; -- unfold collect
    unfold Exterior.collect; simp [Stationary.arm_apply]; ring
lemma stipend_level (U:Link G n):Stipend (U ∘ Lotus.drip n):= ⟨‖U‖,0,norm_nonneg _,fun i=>by rw [liftCost,pow_zero,mul_one]; exact norm_le_pi_norm U (Lotus.drip n i)⟩
lemma blur_tariff (U:Link G n)(T:Tile (edgeL G) r){o:Loc G 1}(h:Knoxville (fame _) σ (0,o) T A)(hs:0<σ): Broc.blur (sieve n T) U=tariffs (fun _=> U ∘ Lotus.drip n) T:= by
   let p v:= T v* ∏ j,U (Lotus.drip n (v j)); have hp: Summable p:= ((pays_product (r:=r) (fun _=> U∘ Lotus.drip n) o hs (fun _=>stipend_level U)).choose_spec.2 T A h).1
   rw [Broc.blueprint]; simp only [Broc.airs,Finset.sum_apply, Pi.mul_apply,Finset.prod_apply]; symm; let f v :chain (wire G n) r:= Lotus.drip n ∘ v
   change (∑' v,p v)=_; rw [←(hp.hasSum.tsum_fiberwise f).tsum_eq,tsum_fintype];refine Finset.sum_congr rfl fun v _=>?_ ; unfold sieve; rw [←tsum_mul_right]; apply tsum_congr; intro i; unfold p; congr 1; exact Finset.prod_congr rfl fun j _=>congr_arg U (congr_fun i.property j)
end YM.FormalBulk08.Spigot
