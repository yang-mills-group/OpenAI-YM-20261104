import YM.MS.SpaceOut.Curt
/-!
# Line symbol smoothing for sectors including a cutoff curve. Piece widths from firstZone waived. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{ I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
  {S T: Scale I}{p:Scale I→QP}{K:I→Set QP}{f:I→QP→F}{h u:I→ℝ}{D:I→Set E}
lemma periodic_τ (hf:Line S located f h) (he:∀ i,pinQ (f i)): Bound S f h:= by
    have H := hf 0; simp only [pow_zero, div_one] at H; refine ⟨ H.smooth,fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:=H.quoted j; refine ⟨ C,hC,k,fun i p ht=>?_⟩; obtain ⟨u,hu⟩:= SpaceOut.use p
    obtain hv:= hk i ( least p ) (handle ..); dsimp only at hv ⊢; conv_lhs=> rw [ hu ];
    rw [ ← iteratedFDeriv_comp_add_right, show (fun q:QP=> f i (q+rep u))=f i from funext ( pin_C (he i ) u ) ]; apply hv.trans; obtain hb:= S.basic_pos i; obtain h0:= S.pos i; obtain hx : h i≥0:= H.nonneg i ( least p ) (handle ..); simp only [Scale.full,Scale.strict]; gcongr; exact le_mul_of_one_le_right hb.le ( S.one_le_weight i p )
lemma Mentor {K:I→ Latch.Edge G}(hK:∀ i,1 ≤ S.length i)(hq:PerK K)(hf:∀ i j:BH G, Line S located (fun t=> K t i j ) (fun t=> S.length t ^ ( (4:ℤ)- wfield i-wfield j ) * h t )) : Fund S K h:= ⟨ ⟨ fun i j=> periodic_τ (hf i j) (fun u=>hq u i j),hf ⟩,hq,hK ⟩
-- attaching unit factors.S.Index merge.
abbrev Benefit (S:Scale I)(P:I→Set E)(f:I→E→F): Prop:= Costs ( S.strict P ) S f ( fun _ _=>1 )
variable {v:I→ Prop}
abbrev leftS (S:Scale I)(v:I→Prop):= borrow S ( (·.val):Subtype v→I )
def taken (T:Cost I E)(v:I→Prop) : Cost (Subtype v) E:= ⟨ fun i=>T.zone i.1,fun i p=>T.cheap i.1 p,fun i p h=>T.one_le i.1 p h ⟩
lemma meet_cost (S:Scale I)(T:Cost I E)(f:I→ E→F)(g:I→ E→ℝ)(h1:Costs (taken T v) ( leftS S v ) (fun i=> f i.1) (fun i=>g i.1))(h2: Costs (taken T (fun i=> ¬v i)) (leftS S (fun i=> ¬ v i)) (fun i=> f i.1) (fun i=>g i.1) ): Costs T S f g := by
    refine ⟨fun i=> (em (v i)).elim (fun h=> h1.smooth ⟨i,h⟩) (fun h=>h2.smooth ⟨i,h⟩), fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= h1.quoted j; obtain ⟨M,hM,b,hb⟩:= h2.quoted j; refine ⟨ C+M,add_pos hC hM,k+b,fun i p hp=>?_ ⟩; have hc:= T.one_le i p hp; have hS:=S.pos i; by_cases hv:v i; · obtain hV: 0≤ g i p:=h1.nonneg ⟨i,hv⟩ p hp; apply le_trans ( hk ⟨i,hv⟩ p hp ); change C*T.cheap i p^k*(g i p*S.length i^j)≤ _; gcongr; linarith; omega
    obtain hV:0≤ g i p:= h2.nonneg ⟨i,hv⟩ p hp; apply le_trans ( hb ⟨i,hv⟩ p hp ); change M*T.cheap i p^b*(g i p*S.length i^j)≤ _; gcongr; linarith; omega
lemma SplitLine (D:I→Set E)(f:I→E→F)(S:Scale I)(g:I→ℝ)(h:Line ( leftS S v ) (fun i=> D i.1) (fun i=> f i.1) (fun i=>g i.1))(he:Line ( leftS S (fun i=> ¬ v i) ) (fun i=>D i.1) (fun i=> f i.1) (fun i=>g i.1)): Line S D f g:= fun j=> meet_cost S ( S.strict D ) _ _ (v:=v) (h j) (he j)
lemma Deposit {f g:I→E→ℂ} (hf:Line S D f h)(he:Benefit S D g): Line S D (fun i p=> g i p*f i p) h:= by intro b; convert ( he.mul (hf b) ) using 1; ext; rw [one_mul]
-- constant f on unit compact delays
lemma sun_b (h:∀ i,1≤ S.length i)(C:Set E) (hC:IsCompact C){f:E→F}(hf:ContDiff ℝ ∞ f): Benefit S (fun _=>C) (fun _=> f):= by
   refine ⟨ fun _=>hf,fun i=>?_ ⟩; obtain ⟨V,hV⟩:= ( hC.image (( hf.continuous_iteratedFDeriv (m:=i) (by exact_mod_cast le_top) ).norm)).bddAbove; refine ⟨max V 1, lt_max_of_lt_right zero_lt_one,0,fun x p hp=>(le_max_of_le_left (c:=1) ( hV (Set.mem_image_of_mem _ hp) )) |>.trans ?_ ⟩; simp only [ pow_zero,one_mul,mul_one ]; exact le_mul_of_one_le_right (zero_le_one.trans (le_max_right ..)) (one_le_pow₀ ( h x )) -- coercion.
--lemma gainK (s:Scale I)(x:E):= x -- remove
end YM.MS.SpaceOut
