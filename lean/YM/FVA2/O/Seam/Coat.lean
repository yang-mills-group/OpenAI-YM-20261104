import YM.FVA2.O.Seam.Gap
/-!
# Assembling genuine `PastPoint` conditions

One layout with all positions separated. `Resembles` allows working in sublayouts
with the same fields/placements. `H_handoff` proves the required vanishing
at negative infinite time for each placement, including the interior/exterior
cluster geometry. Need no uniformity over the parameter space here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse Puff
open scoped Topology ContDiff Interval
variable {G:Gauge} {I W Z A J:Type}{B:Deck G} {K:Booked B}{M:MS_Data G K}{P:Geo I} { Y X F :T ( Glade G I )}
lemma C_copy_b (θ:J→I): compose0 θ (bond G I F Y)= bond G J (compose0 θ F) ( compose0 θ Y ):= funext fun i=> by unfold compose0; simp only [ bond,paired ]; funext p; rw [ Finset.sum_apply, Finset.sum_apply ]; rfl
-- effective projection lemmas
local notation "MΦ"=> M
local notation "Tη"=> Tide.frameF
variable [LinearOrder W][LinearOrder A] {x:Position W I}{ z:Position A I}{ φ:W ↪ A}{R: W→ Label B}{U:A→ Label B}{s:Finset W}{v:Finset A}
structure Resembles (x:Position W I)(R:W→ Label B)(z:Position A I)(U:A→ Label B)(φ:W ↪ A)(s:Finset W): Prop where
    pos i (h:i∈s): z ( φ i )= x i
    art i (h:i∈s): U (φ i)= R i
omit [LinearOrder W] [LinearOrder A] in
lemma resembles_s (h:Resembles x R z U φ s){u: Finset W}(he:u⊆s): Resembles x R z U φ u:= ⟨fun i hi=> h.pos i (he hi),fun i hi=> h.art i (he hi)⟩
lemma reseals (h: Resembles x R z U φ s)(hr:separable z)(hx:separable x) (hc:∀ i∈s, φ i∉v): woods P M z U ((map φ s)∪v)=rootT P M x R s (woods P M z U v):= by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.map_empty,Finset.empty_union,R_nil]
    | insert i s hi ih=>
       rw [ Finset.map_insert, Finset.insert_union,W_step hr ( φ i ) ( fun p=>?_ ),R_step hx i hi,h.pos _ (mem_insert_self ..),h.art i (mem_insert_self ..), ih ( resembles_s h (subset_insert ..) ) ( fun j hj=> hc j (mem_insert_of_mem hj) ) ]; rcases Finset.mem_union.mp p with hp|hp; · obtain ⟨v,hv,h⟩:= Finset.mem_map.mp hp; exact hi (φ.injective h ▸ hv)
       exact hc i (mem_insert_self ..) hp
-- point horizon charges
omit [LinearOrder A] in
lemma pointT (i:I)(hv:separable x): Sweep (Tη Unit (P.η i)) ( compose0 (fun (_:Unit)=> i) ( thins P M x R s ) ) := ahead_n hv ( serves hv ) i
omit [LinearOrder A] in
lemma pointW (i:I)(hv:separable x): Stageable (Tη Unit (P.η i)) ( compose0 (fun (_:Unit)=>i) ( woods P M x R s )) := by unfold woods; rw [ screen_r ]; exact Cool.aroma ( point_m hv i ) rfl ( point_v ( serves hv ) i ) ( tick i x ) _
variable [LinearOrder Z]{ χ:Z ↪ A}{ y:Position Z I}{T0: Z→ Label B}{u:Finset Z}{t: Label B}{m:ℕ}
lemma woods_map (h:Resembles x R z U φ s)(he:separable x)(ht:separable z): woods P M z U (s.map φ)= woods P M x R s:= by obtain hh:= reseals (P:=P) (M:=M) h ht he ( v:=∅ ) (by simp); rw [ Finset.union_empty,W_nil ] at hh; exact hh.trans (( glaze G I ).identityR _)
lemma W_handoff (h:Resembles x R z U φ s)(hh:Resembles y T0 z U χ u)(hp:separable x)(he:separable y)(ht:separable z)(hv:∀ i∈s,φ i∉ map χ u): woods P M z U (( s.map φ )∪ ( map χ u ))= rootT P M x R s (woods P M y T0 u):= by rw [ reseals h ht hp hv,woods_map hh he ht ]
lemma H_handoff (h:Resembles x R z U φ s)(hh:Resembles y T0 z U χ u)(hp:separable x)(he:separable y)(ht:separable z)(hv:∀ i∈s,φ i∉ map χ u): let X:= thicket P M z U (( s.map φ )∪ (map χ u)); PastPoint (( X-rootT P M x R s ( thicket P M y T0 u ) ) m) := by
    intro X; let S:= s.map φ ∪ map χ u; let F:= thicket P M y T0 u; let Y:= woods P M z U S; let L:= rootT P M x R s; have hx : X-L F=(X-Y)-L ( thins P M y T0 u ):= by unfold thins; rw [map_sub]; rw [show Y= L ( woods P M y T0 u ) from W_handoff h hh hp he ht hv]; abel
    rw [show X-rootT P M x R s ( thicket P M y T0 u)=_ from hx]; intro i; let θ (_:Unit):=i;
    obtain h': Sweep ( Tη Unit ( P.η i ) ) ( compose0 θ ( L ( thins P M y T0 u ) ) ):= by unfold L rootT; rw [ C_copy_b θ ]; exact Sweep.rjoint ( pointW i hp ) ( pointT i he );
    exact limitN (P:=Tη Unit ( P.η i )) (F:= compose0 θ ((X-Y)-L (thins P M y T0 u)) m ) ( Thin.sub ( pointT (s:=S) (R:=U) (M:=M) (P:=P) i ht m ) ( h' m ) ) () -- F ambiguity
lemma W_single (a:A)(h:separable z): woods P M z U {a}=singletonM P M ( z a ) ( U a ):= by have hp:= W_step (P:=P) ( R:= U ) (M:=M) h a ( s:=∅ ) ( by simp ); rw [ W_nil ] at hp; simpa using  hp.trans ( ( glaze G I ).identityR _ )
lemma single_t (h:Resembles x R z U φ s)(hp:separable x)(ht:separable z)(a:A)(ha:z a=0)(he:U a=t)(hv:∀ i∈s,φ i≠a): let F:= thicket P M z U ( insert a ( map φ s ) ); PastPoint (( F-rootT P M x R s ( rowM P M t ) ) m) := by
    intro F; have hx := reseals (P:=P) ( M:=M ) h ht hp ( v:={a} ) ( by simpa using hv ); rw [ W_single a ht, singletonM, ha,he,swing_co, Finset.union_singleton ] at hx; rw [ ← hx ]; intro i; exact limitN ( pointT ( R:=U ) ( P:=P ) ( M:=M ) i ht m ) () -- `s`
end YM.FVA2.O.Seam
