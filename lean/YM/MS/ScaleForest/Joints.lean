import YM.MS.ScaleForest.Harvest
/-!
# Bounds, regulator limits and readout of a genuine graph SUM

Contains formula for the INDEPENDENT integral in position space at provided
all-sector closed cumulant (sum of forest-sums). No more internal
specialization of replacements. With Stand (points in range of testing hypotheses,
often just a singleton)
keep the *punctured* series until the finite coefficients
have been determined (`fundraiser`, `costTable`). Prove it for every projected coefficient at every
length; usual subsequent reader only calls the [] slice of sector zero at
zero spectator legs. No implication that anything besides these rank-zero
momentum coefficients have IR limits, at fixed nonzero momentum, etc. We
prove quantitative remainder before using `limUnder` at all. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I W : Type} [TopologicalSpace I] {X Y : Curtain G I} {b : Bool} 

lemma addFringe (a R : ℝ) (ht : Fringe X R a) (hv : Fringe Y R a) : Fringe (X+Y) R a := by
   constructor; intro m; obtain ⟨ H,hH,hP,C,hC,hL⟩:= ht.story m; obtain ⟨F,hF,hf,D,hD,hℓ⟩:= hv.story m;
   refine ⟨ H+F, fun i z hz=> (hH i z hz).add (hF i z hz),hP.add hf,C+D,by positivity,fun z hz i s h=>?_⟩
   simp_rw [Pi.add_apply]; rw [show X z s i m []+Y z s i m []-(H z i+F z i)=(X z s i m []-H z i)+(Y z s i m []-F z i) by abel, add_mul]; exact (norm_add_le ..).trans (add_le_add (hL z hz i s h) (hℓ z hz i s h))
lemma addFront (hF:Frontier X)(he:Frontier Y): Frontier (X+Y):= by intro b hB hp; obtain ⟨R,hR,hT⟩:= hF b hB hp; obtain ⟨S,hS,hU⟩:= he b hB hp; exact ⟨ _, hR.pair hS, addFringe b _ (hT.shrink (min_le_left ..)) (hU.shrink (min_le_right ..))⟩
lemma Frontier.triv : Frontier (0:Curtain G I) := by
   intro b hB hp; refine ⟨ _, Enough.simple, ?_ ⟩; constructor; intro m; refine ⟨ (0:ℂ→I→ℂ),fun _ _ _=>differentiableAt_const _, continuous_const, 1,zero_lt_one, fun z hz i t h=>?_⟩; simp [ (exp_pos _).le ]

abbrev approved (F:Curtain G I) := ∃R:ℝ, Enough R∧∀ s x, Hol (disc R) (fun z=> F z s x)
omit [TopologicalSpace I] in
lemma approve_plus (h:approved X)(hv:approved Y) : approved (X+Y):= by
   obtain ⟨R,hR,hT⟩:= h; obtain ⟨S,hS,hX⟩:=hv; exact ⟨ _,hR.pair hS,fun s x=> ( (hT s x).mono (ball_subset_ball (min_le_left ..))).add ((hX s x).mono (ball_subset_ball (min_le_right ..)))⟩

namespace Planted
variable (μ:ℝ)
/-- Actual forest integrals on all continuation momenta, WITHOUT co-moving shift (undo it). -/
def fundraiser (L: Plan G I b) : Curtain G I:= backing 0 (L.flatMap (forests μ)).sum
/-- Its UV finite part at retained cutoff. -/
def costTable (F: Plan G I b) (i:I) (s:ℝ) := ruby (fun z=> fundraiser μ F z s i) 0
/-- Actual MSbar reading uses the IR endpoint of these projected coefficients,
after that evaluation. -/
def stipend (F:Plan G I b)(i:I):= limUnder atTop (fun s:ℝ=> costTable μ F i s 0 [])

variable [FirstCountableTopology I] (L:Plan G I b)(h:Hired L)
include h
lemma abide : approved (nominal μ L)∧Frontier (nominal μ L)∧Iris (nominal μ L) (L.flatMap (forests μ)).sum := by
   induction L with
   | nil=> exact ⟨ ⟨ _,Enough.simple, fun _ _=> Hol.zero⟩, Frontier.triv,EventuallyEq.rfl⟩
   | cons i L ih=> obtain ⟨ht,hL⟩:= (hire_cons i L).mp h; obtain ⟨hP,hU,hY⟩:= offers μ i ht; obtain ⟨R,hR,hT,hX⟩:= hU (1/2) (by norm_num) (by norm_num); obtain ⟨hx,hf,hS⟩:= ih hL;
                    rw [ show nominal μ (i::L)=resolve μ i+nominal μ L from rfl,List.flatMap_cons,List.sum_append]; exact ⟨approve_plus ⟨R,hR,hT.hol⟩ hx, addFront hY hf, EventuallyEq.add (exactCampaign μ i ht) hS⟩
lemma payoff : Iris (backing 0 (nominal μ L)) (fundraiser μ L) := by
   filter_upwards [(abide μ L h).2.2] with z hz; funext s x; unfold fundraiser backing; rw [hz]


lemma finite_here (s : ℝ)(x:I): Lift (fun z=> fundraiser μ L z s x) (backing 0 (nominal μ L) 0 s x) := by
   obtain ⟨R,hR,hT⟩:= (abide μ L h).1; refine Lift.congr (Lift.trim ((hT s x).grazes s 0) hR.1) ((payoff μ L h).mono (fun z hz=>congr_fun (congr_fun hz s) x))
lemma payable (s:ℝ)(x:I): costTable μ L x s=backing 0 (nominal μ L) 0 s x:= Eq.symm (chosen (n:=0) (finite_here μ L h s x))
lemma throughput : projectV 0 (nominal μ L)= fun i s=> costTable μ L i s 0 := by funext i s; exact congr_fun (payable μ L h s i).symm 0

lemma salary (s:ℝ)(x:I)(m:ℕ)(w:Legs (Shore G m)): Tendsto (fun z=>fundraiser μ L z s x m w) dotty
      (𝓝 (costTable μ L x s m w)):= by rw [payable μ L h]; exact Lift.wind (finite_here μ L h s x) m w

lemma authorized_IR (i:I): stipend μ L i=WindowIR (nominal μ L) 0 0 i∧ Tendsto (fun t:ℝ=> costTable μ L i t 0 []) atTop (𝓝 (stipend μ L i)):= by
   have hx: Frontier (nominal μ L):= (abide μ L h).2.1; obtain ⟨R,hR,hT⟩:= hx (1/2) (by norm_num) (by norm_num);
   obtain ⟨ _,_,_,hU⟩:= Frontier.enter hT (by norm_num) 0; unfold stipend; simp_rw [payable μ L h,backing_nil]; exact ⟨ rfl,hU _ hR.top i ⟩

variable [LinearOrder W] {K:W→ Script G} {V:Palette G}
omit h

/-- Independent forest value on a concrete configuration. Every limit is
taken (UV inside each graph, then Laurent specialization after polar sum,
then big-distance IR). -/
def priceBook (V:Palette G)(μ:ℝ)(K: W→ Script G)(x:W→QP) : Finset W→ T ℂ:= fun S k=>stipend μ (atlas V K (fun i (_:Unit)=> x i) S k).2 ()
/-- General family version. -/
def priceMap (V:Palette G)(μ:ℝ)(K:W→Script G)(x:Rake.Position W I) (i:I) : Finset W→ T ℂ:= fun S k=> stipend μ (atlas V K x S k).2 i
end Planted
end YM.MS.ScaleForest
