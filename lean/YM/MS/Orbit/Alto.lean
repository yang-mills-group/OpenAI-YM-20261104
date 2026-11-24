import YM.MS.Orbit.Fox
/-!
# From presentation to actual finite inversion momentum representation for all mark coefficients.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type} [LinearOrder W]{Z:Lin I}{K: Planet G I}{P: Rake.Site G I}{Y: H_defect G I}{X:Rake.Dance G I W}
 {S:Finset W}{Q:ℕ→I→Law G} {Q': Seeds G I W}{L:I→Side}{u:Faces I}{b:Bool}{n:ℕ}
variable (i:I)
local notation "Ω"=> enterV L b
local notation "Γ"=> σbranch (G:=G) (n:=dimT L i)
local notation "Ψ"=> zoneP L b K i
abbrev Vision (L:I→Side)(b:Bool)(X:Rake.Dance G I W)(i:I)(v:Faces I): Infos W ( FixedMode G (dimT L i) ) :=fun j=>Ag L b i v (X j)
variable (h:Glow K)(he:∀ k,Knits (P k))(hp:∀ S k, Knits ( X S k )) (hf:∀ k, StandGuard L ( P k ) i )
include h he hp hf
lemma Θ_marks : Level Γ Ψ ( Valve L b P Y i ) ( Vision L b X i u S ) n 0 + labels Γ Ψ (Vision L b X i u) S n = PayA L b i u (campus Ω u K P Y ( X S ) X S n ):= by
   let f:=rung Ψ Γ n 0; change f ( Panels L b i P+states L b Y i ) ( Ag L b i u ( X S ) ) + _ = _; rw [ map_add f, LinearMap.add_apply ]; change Level Γ Ψ ( Panels L b i P ) _ _ _ + Level Γ Ψ ( states L b Y i ) _ _ _ + _= _; rw [ level_ba h he hf (hp S), level_d h (hp S) ]; unfold campus labels archB; rw [map_add,map_add]; apply congr_arg₂ _ rfl; rw [ map_sum ]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ map_sum ]; exact Finset.sum_congr rfl fun j hj=> Φ_AA ( hp _ _|>.1 ) h
omit h he hp hf
abbrev W0 (L:I→Side)(b: Bool)(Q: Seeds G I W)(i:I)(v: Faces I): Mate (FixedMode G (dimT L i)) W:= fun S n=> Aspect b L i v (Q S n i)
include h he hp hf
lemma staircase (hx:Crew Ω K P Y u Q' X): CascadeS Γ Ψ ( W0 L b Q' i u ) ( Valve L b P Y i ) ( Vision L b X i u ):= by
   constructor; · funext t; change PayA L b i u ( X ∅ t )=_; rw [ hx.1, Pi.zero_apply,map_zero ]; rfl
   intro S hs i'; obtain ⟨hW,hX⟩:=hx.2 S hs i'; refine ⟨ congr_arg (Aspect b L i u) ( hW i ),?_⟩; rw [ Θ_marks i h he hp hf]; unfold Vision Ag; rw [Function.comp_apply,pay_cycleA (F:=X S i') b L i (hp _ _|>.1 ) h ]; rw [← map_add ]; exact glpto (P:=Aspect b L i u) (GlA b L i u) ( prop_status hX i ) -- parentheses.Status
-- assembly
omit i h he hp hf
structure Circuit (Z:Lin I)(K:Planet G I)(Q:ℕ→ I→Law G)(u: Faces I)(Q': Seeds G I W)(X:Rake.Site G I)(Y:H_defect G I)(P:Rake.Dance G I W) : Prop where
   action : Script Z K Q X
   defect : RecipeD Z K X Y
   crew : Crew Z K X Y u Q' P
   finances : ∀ k,Knits ( X k )
   fund k i : Knits ( Y k i )
   port w t : Knits ( P w t )
omit h he hp hf
lemma CorΦ (Z:Lin I)(u:Faces I)(he: Glow K)(hp:Caps Q)(hv:∀ v,Caps ( Q' v )): ∃ X Y P, Circuit Z K Q u Q' X Y P:= by
    obtain ⟨X,hX,H⟩:= knitB Z he hp; obtain ⟨Y,hY,L⟩:= generateD Z K he H; obtain ⟨P,hP,h⟩:= growM Z K u he H L hv; exact ⟨X,Y,P,hX,hY,hP,H,L,h⟩
lemma C_to (i:I)(hw:Glow K)(hX:Circuit ( enterV L b ) K Q u Q' P Y X)(hp:FaceGuard L Q i): Background ( σbranch ( G:= G ) ( n:=dimT L i ) ) (zoneP L b K i) ( B_init G L b Q i ) ( Valve L b P Y i ) ∧ CascadeS σbranch ( zoneP L b K i ) ( W0 L b Q' i u ) ( Valve L b P Y i ) ( Vision L b X i u ) := by
    have hu:= residentB i hw ( fun i=> hX.finances i |>.1 ) hX.action; have hm(n:ℕ):= tar_guard hw i hu hp n; exact ⟨ dictates i hw hX.finances hX.fund hm hX.action hX.defect, staircase i hw hX.finances hX.port hm hX.crew⟩
-- Endpoint processed later
end YM.MS.Orbit.LogReal
