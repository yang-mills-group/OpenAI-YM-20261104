import YM.RegulatorIR.Clocks.Angles
import YM.RegulatorIR.Capture.Tiles

/-!
# Coupling projection to an average at tied finite mesh

Exact. Needs integrability only of independent normalized pivot fields
(supplied when using H fields, else user supplies). For formal jet precision
use Squares congruences after composing. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Clocks
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Capture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {p r n s d m:ℕ}{G:Gauge}{I W: Type}{f: Side}

lemma alignM(l:ℝ) {P:Room→Writing} (g:Writing)(h:coeff 0 g=0) (H:∀ i:ℕ,IntegrableOn (fun x=>coeff i (P x)) (Centered.court l)): let a(i:ℕ):= weigh (same (l/8)) (l/8) (fun x=>coeff i (P x)); PowerSeries.mk (fun i=> weigh (same (l/8)) (l/8) (fun x=>coeff i ( (P x).subst g)))=(PowerSeries.mk a).subst g:=by
 intro a; ext1 i;rw [coeff_mk]; simp_rw [fun p=>quotes p g h (Nat.le_refl i),map_sum,PowerSeries.coeff_C_mul];unfold weigh accrue; rw [MeasureTheory.integral_finsetSum];swap
 · intro j _; exact (H j).mul_const _
 rw [Finset.sum_div];apply sum_congr rfl; intro j hj; rw [MeasureTheory.integral_mul_const,PowerSeries.coeff_mk]; unfold a weigh accrue; ring

lemma pitchTotal (T:Composite I){P Q:I→Portrait G}{s p:I→ℕ}{τ:ℝ→ℝ}(h:∀ i,T.In i→ pitch (P i) (Q i) f (p i) (s i) τ): pitch (Gather T P) (Gather T Q) f (T.accounts p) (T.accounts s) τ:=by
 induction T with
 | atom t=>exact h t rfl
 | pair A B ih ih'=>
    filter_upwards [ih (fun i hi=>h i (Or.inl hi)),ih' (fun i hi=>h i (Or.inr hi))] with x hA hB
    intro v; let a:= (Gather A P); let b:= Gather B P;let c:= Gather A Q;let d:=Gather B Q
    change x⁻¹^(A.accounts p+B.accounts p)*(vital f a x v 1*vital f b x v 1)=(τ x)⁻¹^(A.accounts s+B.accounts s)*(vital f c _ v 1*vital f d _ v 1); rw [pow_add,pow_add,mul_mul_mul_comm, show x⁻¹^_ * _= _ from hA v,show x⁻¹ ^_ * _= _ from hB v]; exact mul_mul_mul_comm ..

-- Feed natural formal chart .dine. Take universal constant Scale here just a tool. R emitter proof doesn't require global t positivity, unless applying through real derivative transforms. -/

def flat :Scale:= ⟨fun _=>1,rfl,contDiffAt_const,measurable_const,fun _=>zero_le_one⟩
namespace Warp
open Prim Tested
variable (B:Feeds)
abbrev pass (T: Feeds):= T.coupling
def gamma (T:Feeds): PowerSeries ℝ:= PowerSeries.X*tale T.dine
lemma gamma_s : coeff 0 (gamma B)=0:=by simp [gamma, coeff_zero_eq_constantCoeff_apply]
lemma gamma_d : coeff 1 (gamma B)=1:=by rw [gamma,← pow_one (PowerSeries.X: Writing), coeff_X_pow_mul']; simp [B.origin]
def poses : Reset:= Reset.fromR (gamma B) (gamma_s B) (by rw [gamma_d];norm_num)
lemma correct : Script (poses B).bill (pass B):=by
 change Script (PowerSeries.X*tale _) _; apply Script.mul (f:=fun i:ℝ=> i) ?_ (Script.actual B.smooth)
 simpa using! Script.predicts_pow 1
lemma grows : Tendsto (pass B) Tested.germ Tested.germ:=by
 apply tendsto_inf.mpr
 have h: Tendsto (pass B) Tested.germ (𝓝 0):= by
    have hh: Continuous (pass B):= continuous_id.mul B.continuous
    have hp:= hh.tendsto 0; rw [show pass B 0=0 from zero_mul _] at hp; exact hp.mono_left nhdsWithin_le_nhds
 refine ⟨h,tendsto_principal.mpr ?_⟩; exact Tested.eventually_pos.mono fun i hi=> mul_pos hi (B.positive _)
lemma ascends : Relevant B.scale flat (pass B):= Eventually.of_forall (fun x=>by change ((B.dine x)⁻¹^2)/x^2=1/(x*_ )^2; simp [div_eq_mul_inv,mul_pow])
end Warp

-- tie at top including averaged e-coeff only. R arrays often vary coupled derivative but pitch unchanged on overlap. Exact no limit.
def priceRay (T: Binding.Scale)(f:Side)(s:ℕ)(P:Room→ Portrait G) (L:ℝ) : Writing:= PowerSeries.mk (fun i=> weigh (same (L/8)) (L/8) fun x=> plotPT T (vital f (P x)) s i)
lemma plot_read (T: Binding.Scale)(f:Side)(s:ℕ)(P:Room→Portrait G)(L:ℝ): priceRay T f s P L= PowerSeries.mk (fun i=> weigh (same (L/8)) (L/8) fun x=> coeff i (lampF T f s (P x))):=by unfold priceRay lampF; simp
lemma transfer_clock (T S:Binding.Scale)(P Q:Room → Portrait G)(L:ℝ) (r s:ℕ) (τ:ℝ→ℝ)(X: Reset)(hg:Even f.val) (hP:∀ x,Scope r (P x))(hQ:∀ x,Scope s (Q x))(h: Script X.bill τ)(hp:Tendsto τ Tested.germ Tested.germ)(ht: Relevant T S τ)(he:∀ x,pitch (P x) (Q x) f r s τ)(hx:∀ i:ℕ, IntegrableOn (fun x=>coeff i (lampF S f s (Q x))) (Centered.court L)): priceRay T f r P L= (priceRay S f s Q L).subst X.bill:=by rw [plot_read T, plot_read S];simp_rw [fun x=>relabel T S (hP x) (hQ x) hg h X.signal hp ht (he x)]; exact alignM _ _ X.signal hx
end YM.RegulatorIR.Clocks
