import YM.FVA2.O.Project.Track
/-!
# Transport through a fixed change of schemes

Mass and scale conventions already fixed (units of length throughout). Show how
to re-express the claims of OPE via the frame and coupling transformation on
*all* slots of the correlation arrays. See `O/Canon/Give` to use on transformed
Wilson/MS arrays with *one* conversion. Not choosing a post hoc refit at each horizon.
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
variable { G:Gauge }{ I:Type }{n m d k:ℕ}{v t a b:ℝ}
variable {A:Album G}{ V:Arenas G }{H:ℝ→Frames G}{p:Cn}{T U:Cast G}{u:Scan G n}
variable {x:Points n}{y:Points m}{s:Set (Points n)}{ X:Scan G m }
variable { r:ℝ→ Cn }{ f:BLog G n }{ g:Scan G n→ Fable G n }
abbrev ExchangeA (p:Cn)(T:Cast G)(A:Album G): Album G:= marking T ( tune p A )
abbrev holding (p:Cn)( T U:Cast G )( f:BLog G n ): BLog G n := ledger ( fun _=> p ) ( fun _=>T ) ( fun _=>U ) f
abbrev funds (p:Cn)( T U:Cast G )(g:Scan G n→ Fable G n): Scan G n→ Fable G n:= fun u=> holding p T U ( Club g ) u 0
lemma holds (T:Cast G): Town ( fun (_:ℝ)=>T ):= fun _ _ _ _=> Rhythm.const _
lemma clears (q:Cn) : Meter.Clear ( fun (_:ℝ)=> q ):= Pace.formal.fixed _
local notation "V'"=> ExchangeA p T A
local notation "P"=> holding p T U f
local notation "Q'"=> funds p T U g
variable (h:Rooted p)(he:U*T=1)
include h he
lemma funds_good ( hA:∀ i:Scan G n,AllC A i (g i) ): AllC V' u ( Q' u ) := by
    let H:=Club g; have hp:= markup ( f:=H ) ( u:=u ) ( fun _=> calm g hA ) ( holds T ) ( holds U ) ( r:=fun _=>p ) ( clears p ) ( fun _=> h ); refine ⟨ hp.off 0,hp.stays 0,?_⟩; intro s hs hk k d m S v hK hr
    exact budget ( T:=fun _=> T ) ( r:=fun _=> p ) ( c:=fun (i:s× S) (_:ℝ) (u:Scan G n)=> g u i.1.val ) ( z:=fun (i:s× S) (_:ℝ)=> Q' u i.1.val ) ( fun i t=> rate he ) ( holds T ) ( clears p ) ( fun _=> h ) ( fun i j=> ( hA ( decode u i ) ).2.2 s hs hk k d m S ( decode v j ) hK hr ) -- inference for p
lemma paid_w (hA:∀ i:Scan G n,OPEA A i (f i)) : OPEA V' u ( P u ):= by
    refine ⟨ markup ( fun i=> (hA i).toMarkup ) ( holds T ) ( holds U ) ( clears p ) ( fun _=>h ),?_⟩; intro s ht hr k d m S v hx hu; exact budget ( T:=fun _=>T ) ( r:=fun _=>p ) ( c:=fun (i:s× S) t ( w:Scan G n )=> QuoteP w ( f w ) t i.1.val ) ( fun i t=> Gift.total h ( rate he ) ) ( holds T ) ( clears p ) ( fun _=> h ) ( fun i j=> ( hA _ ).through _ ht hr _ _ m S _ hx hu ) -- price orientation `budget` c needs supply explicit
omit he in
lemma observing (hA: Observed A) : Observed V':= by
    intro n p i; unfold ExchangeA marking concert; exact sum_on (fun i x=> _ ) _ ( fun i _ t=> stableV ( A₁:=fun (_:Points n)=> play T p ( decode p i ) ) ( fun _=>continuousOn_const ) ( continual_k ( A:=fun x=> A _ x ( decode p i ) ) ( hA n ( decode p i ) ) h ) _ ) _ -- unused he omit later
omit h he
lemma first_one (h:Law V r H) : seats ( replay ( H 0 ) )=1:= by obtain hp:= spin_k ( slot h 0 ); rwa [show seats ( H 0 )=1 from ( by rw [ show H 0=1 from funext ( h.ground.2 ),seats_one ] ),mul_one] at hp
lemma first_t (h:Law V r H) : ledger r ( Night H ) ( Astro H ) ( Club g ) u 0=g u := by
    funext x b; unfold ledger refund credit Astro Night Club; rw [ h.ground.1, first_one h ]; have he: Astro H 0=1:= by rw [ Astro,show H 0=1 from funext ( h.ground.2 ),seats_one ];
    -- rw .. Ground; zero $p`. credit 1
    rw [ show seats ( H 0 )=1 from he,receipt_K,soloist, X_subst ] -- subst orientation X_subst searches
end YM.FVA2.O.Project
