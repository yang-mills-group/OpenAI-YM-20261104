import YM.MS.Fleet.Natives
/-!
Collapsing any family of finite lattice stencils to one giant local mark. Identity of operators
as cover kernels after `present`: includes all shifts and both possible b.Serve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom
open scoped Topology ContDiff Interval
variable {A I W:Type} [LinearOrder W] {p:Sector A}{G:Gauge}{L:I→Side}{n:ℕ}{b:Bool}{K:Faces I}{U:W→ Actor G}{η:I→ℝ}
-- Subalgebra works with ANY stencils, measure independent

def cylActor (p:Sector A): Actors (Cyl A ℂ):={
   guard := ( Center p ).comap ((Cylinder.Stack A ℂ).subtype) -- inspect
   core := couple p, unit:=piece 1
   holds:= coin_pure 1
   close:= fun _ h _ he=> Pure.prod h he
   identityK:= fun i=> Eq.trans (couple_stone i 1) (one_smul ℂ i)
   identityR:=fun i=> Subtype.ext ( (actor p).identityR i.val )
   turns:=fun _ hx x _=> Subtype.ext (Pure.central hx x.val)
   star_a x y z:= Subtype.ext (times_assoc x.val y.val z.val) }
lemma shipment (L:I→Side)(b:Bool)(i:I)(P:Faces I): Tether (Ocell G L b i P) (cylActor ( DotFlip (G:=G) )) ( actor σbranch ):= by
    constructor; · change Aspect b L i P ( frameL 0 (Cylinder.shade Tone.paywave (piece 1)))=coin 1; rw [ coin_turn, phasecoin, aspect_coin ]
    intro x y; have he : frameL 0 ( run ( couple DotFlip x y ) )=product DotFlip ( frameL 0 (run x)) (frameL 0 (run y)):= by rw [ wave_cost, f_l, f_l,f_l ]; rw [sleeve_prod,lodged_prod]
    exact ( congr_arg ( Aspect b L i P ) he )|>.trans (aspect_pr ..)
omit [LinearOrder W] in
abbrev NatK (G:Gauge):= T (Dot G Cover)
def native (G:Gauge): Actors ( NatK G ):= ( cylActor DotFlip ).stack useN -- namespace
-- hull parameter.Adjust later
variable (c:Berth ( I:=I ) ( W:=W )) (z:W→Cover)(U:W→Actor G)
-- V: array unconverted/spatial.L.
def wordsX (P:Finset W)(A:ℝ): NatK G:= if h:P.Nonempty then if P.card=1 then promote (Lab.Shift (z (P.min' h))) ( U ( P.min' h ) A ) else 0 else 0 -- insert
abbrev Memo (P:Finset W) : Actor G:= fun y=> Cheer ( native G ) ( marked W ) (fun S=>wordsX z U S y) P
lemma word_m (i:W)(x:ℝ): wordsX z U {i} x= promote (Lab.Shift (z i)) ( U i x ):= by unfold wordsX; simp only [Finset.singleton_nonempty,↓reduceDIte, Finset.card_singleton, ↓reduceIte, Finset.min'_singleton ]
lemma word_e {S:Finset W}(hx:S.card≠1)(x:ℝ): wordsX z U S x=0:= by
    unfold wordsX; by_cases he:S.Nonempty; · rw [dif_pos he, if_neg hx]
    rw [dif_neg he]
-- Torus program. Show purity
local notation "S"=> Aspect b L -- notation.Boggle
variable {k:Team} {s:Finset W}
lemma ships (η:I→ℝ)(P:I→Cover)(L:I→Side)(i:I)(b:Bool)(k:ℕ): Font σbranch ( W0 L b (goalsK c η U) i P ) s k=Ocell G L b i P ( Memo (fun w=> c w i) U s ( η i ) k ):= by
    let A:=Ocell G L b i P; let U'(s):=wordsX (fun w:W=> c w i) U s (η i); have he : pointL ℕ A ∘ U' = W0 L b ( goalsK c η U ) i P := by
       funext s k; change A ( U' s k )= Aspect b L i P (goalsK c η U s k i ); by_cases h : s.card=1; · obtain ⟨t,rfl⟩:= Finset.card_eq_one.mp h; rw [ goals_m,vFrame ]; unfold U'; rw [ word_m ]; rfl
       rw [ show U' s=0 from word_e _ U h _, goals_t _ _ h, Pi.zero_apply,Pi.zero_apply, Pi.zero_apply,map_zero,map_zero ]; -- eq.independent
    unfold Font; rw [ ← he ]; exact ( congr_fun ( ( ( ( shipment (G:=G) L b i P ).Extrapolation useN ).figure ( marked W ) U' s )) k ).symm -- parentheses
lemma expect_n (L:I→Side)(p:Faces I)(u: Dot G Cover)(b:Bool)(i:I)(h:Tuned u 0): Pure σbranch false ( Ocell G L b i p u ):= by
    let A:= run u; have he : Pure DotFlip false A:= tied.pure u ( h.parity ghostParity ); have hv : Pure σbranch false (anchor G (dimT L i) (p i) ( sleeve lace A )):= by
        intro l hp; rw [ spell_anchor, lodg,sleeve_here, he _ ?_,mul_zero,mul_zero ]; exact Λ_d l ▸ hp -- signature
    change Koszul.Pure σbranch false (Aspect b L i p (frameL 0 (run u))); rw [ eFrame,As_h ]; cases b; exact hv; exact Rim _ _ _ hv
end YM.MS.Fleet
