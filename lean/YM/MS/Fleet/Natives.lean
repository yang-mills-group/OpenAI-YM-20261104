import YM.MS.Fleet.Powers
import YM.MS.Puff.Story
/-!
Packing cover marks: aspect morphism sends any moment series at a common anchor to each
prescribed finite regulator's actual product. In particular the parity assumptions for Puff.Mom
hold, even when a mark contains a BV exact adjustment, no assumption on source positions. (Separation
will be needed to identify exact drop on cover.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open Cylinder Lab High Program Logarithm Wind Menus
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom
open scoped Topology ContDiff Interval
variable {A I W:Type}{p:Sector A}{G:Gauge}{L:I→Side}{n:Side}
local notation "pE"=>field ( parity (C:= G.ColorIndex) (A:=Axis) )
lemma lodged_prod (A:Cover)(F H:Law G): lodging A ( product pE F H )= product pE ( lodging A F ) ( lodging A H ):= by
   ext w; simp_rw [lodg, scattered, lodg]; let K:=allocate (field parity) w ( R:=ℂ); change _* K _ = _; rw [ ← smul_eq_mul, ← map_smul ]; refine scatter_congr _ _ _ _ ( fun x y hx=>?_ ); simp only [ Pi.smul_apply, smul_eq_mul, ← split_net hx,be_mom ]; ring -- sdependent
lemma sleeve_prod (F H:Law G) : sleeve lace ( product pE F H )= product pE (sleeve lace F) (sleeve lace H) := by
    ext w; simp_rw [sleeve_here,scattered,sleeve_here]; let K:=allocate pE w ( R:=ℂ); change _* K _ =_; rw [ ← smul_eq_mul, ← map_smul ]; refine scatter_congr _ _ _ _ (fun x y hx=>?_ ); simp only [Pi.smul_apply,smul_eq_mul, ← split_hook hx ]; ring
lemma phasecoin (A:Cover) (c:ℂ): frameL A (G:=G) ( coin c )=coin c:= by rw [f_l]; ext l; cases l with| nil=> rw [home_0,sleeve_here]; exact one_mul _| cons i l=> simp [lodg, Koszul.coin]
lemma spell_anchor (A:Cover)(F: Law G)(w:Legs (FixedMode G n)): anchor G n A F w= lodging A F (stage w):= by rw [chase_now,φ_s,Orbit.point,lodg]
-- restriction
lemma ptrprod (F H:Law G): Vμ (product pE F H) n=product σbranch ( Vμ F n ) ( Vμ H n ):= by
    -- natural pull along list map with parity preservation. `wander`
    ext w; simp_rw [Orbit.point,scattered,Orbit.point]; -- scatter.L
    exact scat_δ .. 
lemma anchor_pr (A:Cover)(F H:Law G): anchor G n A ( product pE F H )= product σbranch ( anchor G n A F ) ( anchor G n A H ):= by
    have he (F:Law G):anchor G n A F=Vμ (lodging A F) n:= funext fun i=>spell_anchor A F i; rw [he,he F,he H,lodged_prod,ptrprod]
lemma aspect_pr (L:I→Side)(b:Bool)(i:I)(p:I→Cover)(F H:Law G): Aspect b L i p ( product pE F H )= product σbranch ( Aspect b L i p F ) ( Aspect b L i p H ):= by
    simp_rw [As_h, anchor_pr]; cases b; · rfl
    exact Cog.rotate_p ..
lemma aspect_coin (P:Faces I)(b:Bool)(i:I)(c:ℂ): Aspect b L i P ( G:=G ) (coin c)= coin c:= by
    have he:( anchor G (dimT L i) ( P i ) ( coin c ) ) = coin c:= by ext w; cases w with| nil=> rw [spell_anchor, Orbit.stage, List.map_nil,home_0]; rfl| cons i l => rw [ spell_anchor,lodg ]; simp [Orbit.stage,coin]; -- ??
    rw [ As_h, he ]; cases b; rfl; let U:= iota G (dimT L i); change U.wheel _ _ _=_; apply ext_D ?_ ?_ -- check
    · exact wheel_nil ..
    intro x; rw [wheel_rule,blend_at,Cylinder.coin_nod,Cylinder.coin_nod,map_add,smul_zero,smul_zero,map_zero,add_zero]
-- stencil
variable {b:Bool}{P:Faces I}
abbrev Ocell (G:Gauge)(L:I→Side)(b:Bool)(i:I)(P:Faces I): Dot G Cover→ₗ[ℂ] BL (FixedMode G (dimT L i)) := Aspect b L i P ∘ₗ ( frameL 0 ∘ₗ Tone.run )
lemma vFrame (A:Cover)(F:Dot G Cover): frameL A ( run F )=frameL 0 ( run (Lab.Shift A F) ):= by
   rw [f_l,f_l, pure]; ext w; rw [lodg,sleeve_here,sleeve_here,movement,Tone.rights]; exact mul_left_comm .. -- which T.r
lemma eFrame (F:Dot G Cover) : frameL (0:Cover) ( run F )=sleeve lace ( run F ):= by rw [f_l,pure]
-- guarded Stencil.Cylinder algebra
abbrev CapeN (G:Gauge)(I:Type):= Dot G I
end YM.MS.Fleet
