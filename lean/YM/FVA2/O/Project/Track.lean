import YM.FVA2.O.Project.Only
/-!
# Perturbative reexpression for a shape already scaled by a fixed positive radius

Thus applying the FAR rule directly on a shrunk shape will give the OPE coefficient
of the unscaled shape with that radius argument. Prove the shift-in-the-logarithm
formula using uniqueness of the NEAR scheme. No finite-mesh assertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Project
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind
variable { G:Gauge }{I:Type}{n m d k:ℕ}{v t a b:ℝ}{x:Points n}{y:Points m}
variable { V:Arenas G }{ A:Album G }{ u:Scan G n }{X:Scan G m}{ r:FLog G n }{ s:Set (Points n) }
lemma fee_x (a b n:ℝ): Score.fee a n * Score.fee b n = Score.fee (a+b) n:= by unfold Score.fee; rw [← Complex.ofReal_mul, ← Real.exp_add,neg_add,add_mul]
abbrev Delay (a:ℝ)(u:Scan G n)(r:FLog G n): FLog G n:= fun t x b=> pack u (-a) (r (t-a) ( squeeze a x )) b
local notation "p"=> Delay a u r
lemma stamp_q : QuoteP u p t x= QuoteP u r (t-a) ( squeeze a x ):= by funext q; unfold Delay QuoteP pack; rw [ ← mul_assoc, ← map_mul,fee_x ]; rfl
lemma zero_t (r:FLog G n)(u:Scan G n): QuoteP u r 0 = r 0:= by funext x b; unfold QuoteP pack Score.fee; rw [neg_zero,zero_mul,Real.exp_zero, Complex.ofReal_one,map_one,one_mul]
lemma time_a (t a:ℝ)(x:Points n): squeeze (t-a) ( squeeze a x )=squeeze t x:= by unfold squeeze; rw [ ← mul_smul, ← Real.exp_add, ← neg_add,sub_add_cancel ]
lemma positions : Submit A u X t p d x y = Submit A u X ( t-a ) r d ( squeeze a x ) y := by unfold Submit; rw [ stamp_q,time_a ]
lemma rain_shift {f:I→ℝ→ℂ}(h: Rain a f)(b:ℝ): Rain a (fun i t=> f i (t-b)) := by
    obtain ⟨C,hC,k,H⟩:= h; let x:ℝ:=1+|b|
    have hx : 0<x:= by unfold x; positivity
    refine ⟨ C*( x^k*Real.exp (a*b) ),(by positivity),k,?_⟩; obtain he : Tendsto ( fun i:ℝ=> i-b ) atTop atTop:= tendsto_id.atTop_add tendsto_const_nhds -- orientation sign
    filter_upwards [ he.eventually H,eventually_ge_atTop (0:ℝ),eventually_ge_atTop b ] with t ht h H i; apply le_trans ( ht i ); have hh: 1+(t-b) ≤ (1+t)*x:= (by unfold x; nlinarith [ abs_nonneg b, neg_le_abs b ]); unfold post; rw [ show -a*(t-b)=-a*t+a*b from (by ring), Real.exp_add ]; apply le_trans ?_ ( show C*( ( (1+t)*x )^k * ( Real.exp (-a*t)*Real.exp (a*b) ) ) ≤ _ from (by rw [ mul_pow ]; exact le_of_eq (by ring) ) ); gcongr
lemma shifting (h: OPEA A u r)(he:IsCompact s)(hp:s⊆conf n): Exteriors A s p u k 1 d:= by
    intro m K v hK hr i hn; simp_rw [ positions ]; let J:= squeeze a '' s; obtain he : IsCompact J := he.image ( show Continuous ( squeeze (n:=n) a ) from continuous_const_smul ( rexp (-a) ) ); obtain hh:= h.through J he ( image_subset_iff.mpr ( fun i ht=> squeeze_away ( hp ht ) a )) k d m K v hK hr i hn; let F:s× K→ J× K:= fun x=> (⟨ squeeze a x.1.val, Set.mem_image_of_mem _ x.1.property ⟩,x.2 ); exact rain_shift ( hh.pull F ) a -- CE
lemma stamp_R (h:Markup r): Patches_e ( Delay a u r ) s k d:= by
    intro i _ j _ x hx u; obtain ⟨C,hC⟩:= h.poly ( Score.own u ) j; have ht:= ( hC ( squeeze a x ) ).translate a; unfold Delay pack; simp only [ coeff_C_mul ]; exact Rhythm.mul ( Rhythm.const _ ) ⟨ _,ht ⟩
local notation "A0" => install V
lemma timed (h:Ground V)(he:Regular V)(hp:OPEA A0 u r)(hx: x∈ conf n): QuoteP u r t x=QuoteP u r (t-a) ( squeeze a x ):= by
    rw [ ← stamp_q ]; have hu : IsCompact ({x}:Set (Points n)):= isCompact_singleton; let S:= ({x}:Set (Points n)); have hS:S⊆conf n:= singleton_subset_iff.mpr hx; suffices h : r t x= p t x by unfold QuoteP; rw [h]
    funext q; ext i
    exact uniqueness ( u:=u ) ( s:={x} ) h he ( fun _ _=> hp.through _ hu hS _ ( i+1 ) ) ( fun _ _=> shifting hp hu hS ) hp.toMarkup.patch ( stamp_R hp.toMarkup ) zero_lt_one x ( mem_singleton x ) q le_rfl i ( Nat.lt_succ_self i )
lemma onward (h:Ground V)(he:Regular V)(hp:OPEA A0 u r)(hx:x∈conf n): QuoteP u r t x = r 0 (squeeze t x):= by rw [ timed ( a:=t ) h he hp hx, sub_self,zero_t]
end YM.FVA2.O.Project
