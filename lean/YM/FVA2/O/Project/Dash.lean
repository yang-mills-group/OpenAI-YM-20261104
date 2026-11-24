import YM.FVA2.O.Project.Bank
/-!
# Dilation transport from FAR to NEAR

From the far estimate on the unit input shapes; use the power weight factors for the whole
list and the all-orders scale law. This file works coefficientwise with no derivative bounds.
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
variable { G:Gauge }{I:Type}{n m d k i:ℕ}{a t:ℝ}{ u:Scan G n }{ v:Scan G m }
variable { r:ℝ→ Cn }{ T U:ℝ→ Cast G }{ s:Set (Points n) }{K:Set (Points m)}
variable { x:Points n }{ y:Points m }{ z:FLog G n }{ p:Bill G }
variable { V:Arenas G }{ A:Album G }{ H:ℝ→Frames G }
local notation "V0"=> install V
abbrev Astro (H:ℝ→Frames G) : ℝ→ Cast G := fun i=> seats ( H i )
abbrev Night (H:ℝ→Frames G) : ℝ→ Cast G:= fun i=> seats ( replay ( H i ) )
abbrev Stellar (r:ℝ→Cn)(T:ℝ→ Cast G)(A:Album G)(t:ℝ): Album G:= marking ( T t ) ( tune ( r t ) A )
local notation "Vt"=> Stellar r ( Night H ) V0 t
variable (h:Law V r H)(he:Regular V)
include h he
lemma step_party (t:ℝ)( x:Points n )(u:Scan G n)( y:Points m )(v:Scan G m) : party V0 ( squeeze t x ) y u v= Acres (-t) (totalG u+totalG v) * party ( Stellar r ( Night H ) V0 t ) x ( squeeze (-t) y ) u v:= by unfold party; rw [ crossN,adjust_clock h he,totalW ]; -- defeq rfl?
lemma step_lamp (u:Q G): lonelyG V0 y u v = Acres (-t) (heft u+totalG v)*lonelyG Vt (squeeze (-t) y) u v:= by
    obtain hx:= step_party h he t 0 ( Single u ) y v; rw [ squeeze,smul_zero,totalOne ] at hx; exact hx -- name apostrophes
omit h he
lemma Fee_H (t:ℝ)(b e w:ℕ): PowerSeries.C ( Score.fee t ( (w:ℝ)-( e:ℝ ) )) * Acres (-t) (w+b )= Acres (-t) (e+b):= by
    unfold Acres; rw [← map_mul]; unfold Score.fee; rw [← Complex.ofReal_mul, ← Real.exp_add ]; congr 3; push_cast; ring
lemma Lamp_link (A A':Album G)(hr:∀ y:Points m, ∀ u:Q G, lonelyG A y u v= Acres (-t) ( heft u+totalG v )* lonelyG A' ( squeeze (-t) y ) u v ): Lamp A k y v ( pack u t p )= Acres (-t) ( totalG u+totalG v )* Lamp A' k ( squeeze (-t) y ) v p:= by
    unfold Lamp Settle; simp_rw [hr,pack,Finset.mul_sum ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by rw [ mul_mul_mul_comm, Fee_H ] -- check lemma order
include h he
lemma dashing ( t:ℝ )( y:Points m )( x:Points n ): Submit V0 u v t z k x y= Acres (-t) ( totalG u+totalG v )*Basket ( Stellar r ( Night H ) V0 t ) u v ( z t x ) k x ( squeeze ( -t ) y ):= by unfold Submit Basket QuoteP; rw [ Lamp_link V0 ( Stellar r ( Night H ) V0 t ) ( hr:=fun y u=> step_lamp h he u ), step_party h he,mul_sub ]
-- Estimates geometry-general transfer through markingt and tune, then dilation phase.
omit h he
section estimate
variable { x:I→ℝ→ Points n }{ y:I→ℝ→ Points m }
variable { z:I→ℝ→ Bill G }{ c:I→ℝ→ Draft G n }
lemma budget (h:∀ i:I,∀ t:ℝ,Gift ( T t ) ( r t ) u ( c i t ) ( z i t ))(hv:Town T)(hp:Meter.Clear r)(hq:∀ t,Rooted (r t)) (hx: ∀ (j:LivesP u)(w:LivesP v), ChargeP k a ( fun i t=> Basket A ( decode u j ) ( decode v w ) ( c i t ( decode u j ) ) d ( x i t ) ( y i t ) )): ChargeP k a ( fun i t=> Basket ( Stellar r T A t ) u v ( z i t ) d ( x i t ) ( y i t ) ) := by
    simp_rw [ Stellar, exchange A ( h _ _ ) ( hq _ ) ]; refine cost_tag hv u _ ( fun i=> cost_tag hv v _ fun j=>?_ ); exact ChargeP.Pact ( hx i j ) ( ChargeP.clean hp ) ( fun _ t=> hq t ) -- meaning section
end estimate
variable { g: Scan G n→ Fable G n }
include h he
local notation "P0"=> ( ledger r ( Night H ) ( Astro H ) ( Club g ) u )
lemma Honor (hr:∀ i:Scan G n,AllC V0 i ( g i ))(hp:IsCompact s)(hx:s⊆conf n): Exteriors V0 s P0 u k 1 d:= by
    intro m K v hK hV; unfold Near; simp_rw [ dashing h he ]
    have hu (t:ℝ): Astro H t * Night H t=1:= spin_v ( slot h t ); let J:=s×K; let e:ℝ:= -( ( (totalG u+totalG v : ℕ ):ℝ ) ); let b:ℝ:= (k:ℝ)+1 + (totalG v:ℝ)
    have ht : ChargeP d b ( fun (i:J) t=> Basket (Stellar r (Night H) V0 t) u v ( P0 t i.1.val ) k i.1.val ( squeeze (-t) i.2.val ) ):= budget ( c:=fun (i:J) (_:ℝ) ( u0:Scan G n )=> g u0 i.1.val ) ( fun i t=> rate (hu t) ) ( rhythm_b h ) h.smooth ( fun _=> ( h.led _ ).start ) ( fun i j=> (hr ( decode u i ) ).2.2 s hp hx k d m K ( decode v j ) hK hV )
    exact ChargeP.grow ( ChargeP.joint ( a:=e ) reflectV ht ) ( by unfold b e; push_cast; linarith )
lemma shines (hr:∀ i:Scan G n, AllC V0 i (g i)) : OPEA V0 u P0:= ⟨ markup ( fun _=> calm g hr ) ( rhythm_b h ) ( rhythm_v h ) h.smooth ( fun _=> ( h.led _ ).start ), fun _ H' hp _ _=> Honor h he hr H' hp ⟩ -- names
end YM.FVA2.O.Project
