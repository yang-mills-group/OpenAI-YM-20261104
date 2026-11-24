import YM.FormalOPE.RG10.Horizon.Confine
import YM.FormalOPE.RG10.Horizon.Foreshorten
/-! # Adjusted WilsonX near/far conversion

Grading is exactly the common radiation orientation of Pose.R. Fields are renewed each time a
correlation is read in different X units; no assuming no charge on nonlinear exterior groups.
Precision edition r used simultaneously on all positions at all finite height h for the indicated
suite. Limit actions don't need an `Attaches` on the new geometry; permits using grown or
shrunken test positions -- but calling a step-schedule estimate in a *joint scaling limit* needs
more. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
    (T:Tuned R Z) (M: Halo) (x:Fin m→ Seats F d)(E:Fore m) (hM :Valid F h M){S:Finset (Vantage F)} {B : Seats F h}
    (s t:ℝ)
local notation "θ" => R.flow.warp
local notation "W" => winter R Z M
local notation "V" => profit R Z M
local notation "x'" => trail R s ∘ x
local notation "E'" => compress s E

lemma relaying : trail R s (trail R t B)=trail R (t+s) B:=by
 unfold trail;
 have he (v:Seats F h)(M:Matrix (Deck F h) (Deck F h) fps): θ s ∘ (v ᵥ* M) = (θ s ∘ v) ᵥ* M.map (θ s) := funext (fun i=>RingHom.map_vecMul ..)
 rw [he,Matrix.vecMul_vecMul]; simp_rw [Grade.Rails.drive]; rw [Passe.station_law]
 congr 1
 change (RingHom.comp (θ s) (θ t) ∘ B) = _; rw [R.ok.uses,add_comm]

@[simp] lemma at_trail (v : Seats F h) : trail R 0 v=v:= by
 have he:= relaying (R:=R) (B:=v) (-0) (s:=0);
 simp only [neg_zero,zero_add] at he
 exact he.symm.trans (by simpa using (unfold_trail (R:=R) v 0)) -- order ???

private lemma numbered (q: Panel.Consumer.Vantage F) : trail R s ∘ (trail R (-t) ∘ q.fields) = (trail R (-(t-s)) ∘ q.fields):= by
  ext1 i; simp only [Function.comp_apply,relaying,neg_sub]; rw [add_comm,sub_eq_add_neg]

include T
lemma movement (q : Panel.Consumer.Vantage F) : θ s (burst R Z q t E x)=burst R Z q (t-s) E' x':= by
 by_cases he : E.budget < Real.exp t * q.rear.gap
 · rw [burst,burst,dif_pos he, Panel.moved _ _ T.street, numbered, Arrangements.contracted]; rw [dif_pos (capacity s t E q.rear|>.1 he)]
 simp_rw [burst,dif_neg he,dif_neg (mt (capacity s t E q.rear).mpr he), map_zero]

lemma infers (q : Panel.Consumer.Vantage F) : θ s (imply R Z q t h B) = imply R Z q (t-s) h (trail R s B):= by
 rw [imply, seen_on,Panel.found, Panel.moved _ _ T.street,numbered,silver,dilations]
 rw [imply,seen_on]; rfl

include hM
private lemma intercepts (j:Deck F h) : imply R Z (exhibit M j) t h (W x E h t) = burst R Z (exhibit M j) t E x:= by rw [heartbeat,winter,Matrix.vecMul_vecMul,M.left R Z h t T.street hM, Matrix.vecMul_one]

theorem forecasts_scaled : W x' E' h (t-s)=trail R s (W x E h t):= by
 let V' := (t-s); let Z':=trail R s (W x E h t)
 have he : (fun (i:Deck F h)=> burst R Z (exhibit M i) V' E' x') = Z' ᵥ* M.Lens R Z h V':= funext (fun i=>by unfold V'; rw [← movement T x E,← heartbeat,← infers T, intercepts T M x E hM]); -- type
 unfold winter; erw [he, Matrix.vecMul_vecMul,M.right R Z h V' T.street hM, Matrix.vecMul_one]; rfl
omit T hM
/-- Through (publication) order on a coefficientwise height-h message. -/
def Clears (r:ℕ) (K : ℝ→Seats F h) (v: Seats F h) := ∀ i, ∀ n≤r, Tendsto (fun t=>coeff n (K t i)) atTop (𝓝 (coeff n (v i)))
def Assessed (r:ℕ)(u : ℝ → fps) (A:fps) := ∀ n≤r, Tendsto (fun i=>coeff n (u i)) atTop (𝓝 (coeff n A))
namespace Assessed
variable {f g:ℝ → fps}{a b:fps}(hf:Assessed r f a) (hg:Assessed r g b)
include hf hg
lemma added : Assessed r (f+g) (a+b):=by intro n hn; simpa using! (hf n hn).add (hg n hn)
lemma multiplied : Assessed r (f*g) (a*b):=by intro n hn; simp_rw [Pi.mul_apply, coeff_mul]; exact tendsto_finsetSum _ fun i hi=> (hf i.1 (by obtain h:=mem_antidiagonal.mp hi; omega)).mul (hg i.2 (by obtain h:=mem_antidiagonal.mp hi; omega))
omit hf hg
lemma fixed (a:fps) : Assessed r (fun _=>a) a:= fun _ _=>tendsto_const_nhds
variable {I:Type*}{u:I→ℝ→fps}{v:I→fps}
lemma sums (s:Finset I) (h:∀ i∈s, Assessed r (u i) (v i)) : Assessed r (fun t=>∑ i∈s,u i t) (∑ i∈s,v i):= by intro n hn; simp_rw [map_sum]; exact tendsto_finsetSum _ fun i hi=> h i hi n hn
include hf
lemma exposed : Assessed r (fun t=> θ s (f t)) (θ s a):= by
 intro i hi; simp_rw [Flow.through]; exact (hf i hi).add (tendsto_finsetSum _ fun i' hi'=> (hf i' (le_trans (mem_range.mp hi'|>.le) hi)).mul_const _)
lemma times_const (b:fps): Assessed r (fun t=>f t*b) (a*b):= multiplied hf (fixed _)
end Assessed
include T hM
-- use shift t↦ t-s in the forecast before limits
lemma assessing (hα: Clears r (W x E h) (V x E h)) : Clears r (W x' E' h) (trail R s (V x E h)) := by
 have ht (i): Assessed r (fun t=> trail R s (W x E h t) i) (trail R s (V x E h) i) := Assessed.sums (u:=fun (i':Deck F h) t=> θ s (W x E h t i') *R.drive s h i' i) _ fun i' _=> (Assessed.exposed s (hα i')).times_const _
 have he(t:ℝ): W x' E' h t= trail R s (W x E h (t+s)):=by
    have hp:=forecasts_scaled T M x E hM s (t+s); rwa [add_sub_cancel_right] at hp
 intro i n hn; simp_rw [he]; exact (ht i n hn).comp (tendsto_atTop_add_const_right atTop s tendsto_id)

theorem pays_scaled (hα : Clears r (W x E h) (V x E h)) (i : Deck F h)(n:ℕ) (hn:n≤r) :
   coeff n (profit R Z M x' E' h i)=coeff n (trail R s (profit R Z M x E h) i):= by
 rw [corner]; exact (assessing T M x E hM s hα i n hn).limUnder_eq
end YM.FormalOPE.RG10.Clearing
