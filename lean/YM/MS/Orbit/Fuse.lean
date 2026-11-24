import YM.MS.Orbit.Coding
/-!
# Window change. Linear transfer of time-labelled curve. For b= false & true
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
open LogReal
variable {A W E I:Type}{G:Gauge}{s:Lin I}{ F H:Glade G I}{ L:I→Side}{ P:Planet G I}{X:Rake.Site G I}
   {Q:ℕ→I→Law G}{a:I}
abbrev Tape (Q: Therapy (Lane4 G) A) (i:I) : Glade G I →ₗ[ℂ] OM A:={
    toFun F:= fun t=> Q (F i t)
    map_add' _ _:= by funext t; exact map_add Q ..
    map_smul' u f:= by funext t; exact map_smul Q .. }
variable (L)
abbrev dimT (L:I→Side)(i:I) := periodN ( L i )
abbrev YLift (L:I→Side)(i:I):= Tape ( Bulk G ( dimT L i ) ) i -- G implicit
abbrev WLift (L:I→Side)(i:I)(W: I→Cover):= Tape ( anchor G (dimT L i) (W i)) i
abbrev zoneP (b:Bool) (P:Planet G I)(i:I): Lines ( FixedMode G (dimT L i)):= primary G (dimT L i) b (P i)
lemma σ_plan (b:Bool)(h:Toned F)(i:I): YLift L i ( CPlan ( enterV L b ) P F )= Static ( zoneP L false P i ) ( YLift L i F ) := funext fun t=> (pc_bulk (h.sound i t)) |>.symm
lemma σ_step (h: Glow P)(hp:Toned F)(hx:Toned H)(i:I): YLift L i ( expJ P F H )= TypeTouch σbranch (zoneP L false P i) (YLift L i F) (YLift L i H):= funext fun t=> ( BB (h.proper i t) (hp.sound i t) (hx.sound i t) (n:=dimT L i))|>.symm
variable {L}
abbrev BulkB (L:I→Side)(B:Rake.Site G I)(i:I): Series (FixedMode G (dimT L i)):= (YLift L i) ∘ B
abbrev StartB (G:Gauge)(p:I→ Side)(Q:ℕ→I→ Law G)(i:I): SpecB (FixedMode G ( dimT p i )):= fun n=> Bulk G (dimT p i) ( Q n i )
lemma Φ_level (i:I)(h:Glow P)(hp:∀ n,Toned (X n))(n:ℕ): YLift L i ( groups P X X n ) = Level σbranch ( zoneP L false P i ) (BulkB L X i) ( BulkB L X i ) n 1:= by unfold groups pathU Level; rw [map_sum]; exact Finset.sum_congr rfl (fun j hj=> σ_step L h (hp _) (hp _) i)
variable {b c:Bool} -- earlier variable (b) needs type explicit
lemma residentB (i:I)(h:Glow P)(hp:∀ n,Toned (X n))(hx:Script ( enterV L c ) P Q X): Background σbranch (zoneP L false P i) ( StartB G L Q i ) (BulkB L X i):= by
   constructor; · unfold BulkB; rw [ Function.comp_apply, hx.1,map_zero ]; -- defeq
   intro n he; obtain ⟨ hm, hV⟩:= hx.2 n he; refine ⟨ congr_arg (Bulk G (dimT L i)) (hm i),?_⟩; rw [ ← Φ_level i h hp n ]; let U:=YLift (G:=G) L i; rw [ ← map_smul U,show Static (zoneP L false P i) ((BulkB L X i) n)= U ( CPlan ( enterV L c ) P ( X n ) ) from (σ_plan L c (hp n) i).symm, ← map_add U ]; exact glpto (gl_Bulk G (dimT L i)) (prop_status hV i)
abbrev FaceGuard (L:I→Side)(Q:ℕ→ I→Law G)(i:I): Prop:= ∀ n,(iota G (dimT L i)).Invar ( StartB G L Q i n ) ∧ Pure σbranch false ( StartB G L Q i n )
abbrev StandGuard (L:I→Side)(Q:Glade G I)(i:I): Prop:= ∀ t,(iota G (dimT L i)).Invar (YLift L i Q t) ∧ Pure σbranch false (YLift L i Q t)
lemma tar_guard (h:Glow P)(i:I)(hp:Background σbranch (zoneP L false P i) ( StartB G L Q i ) (BulkB L X i))(hz:FaceGuard L Q i)(j:ℕ): StandGuard L (X j) i:= by
    intro t; let U:= ( iota G (dimT L i) ); have he(a:ℝ): U.phase ( zoneP L false P i a ):= riverOK (h.proper i a|>.pin) ( h.proper i a |>.gov ); exact ⟨ fixed ( mirrorACT he ) hp (fun i'=> hz i'|>.1) j t,pastStand hp ( fun t=> evenK (h.proper i t|>.close)) ( fun i=> hz i|>.2 ) j t ⟩ -- defeq
end YM.MS.Orbit
