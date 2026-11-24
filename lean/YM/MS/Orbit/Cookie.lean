import YM.MS.Orbit.Fuse
/-!
# ReadT.Lifts & operation-level pointwise.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G: Gauge}{A W I:Type}{L:I→Side}{b:Bool}{Z:Lin I}{F H:Glade G I}{P: Planet G I}
 {v w:I→Cover} {i:I}{n j:ℕ} -- fail
abbrev Lag (L:I→Side)(b:Bool)(i:I) := Present b G (dimT L i)
abbrev Scan (b:Bool)(L:I→Side)(i:I): Law G→ₗ[ℂ] Than G (dimT L i):=(Lag L b i).comp ((pay b) • ( Bulk G (dimT L i)))
abbrev Aspect (b:Bool)(L:I→Side)(i:I)(v: Faces I): Law G→ₗ[ℂ] Than G (dimT L i):= ( Lag L b i ).comp ( anchor G ( dimT L i ) (v i ))
lemma Vexp (t:Law G): Scan b L i t=Lag L b i (pay b • Bulk G (dimT L i) t):= by rw [Scan,LinearMap.comp_apply,LinearMap.smul_apply]
lemma As_h (t:Law G): Aspect b L i v t=Lag L b i (anchor G ( dimT L i ) ( v i ) t):= rfl
lemma GlB (b:Bool)(L:I→ Side)(i:I): Glance (Scan (G:=G) b L i) := by
   obtain h:=gl_Bulk G (dimT L i); obtain hp:= ( gl_read (iota G (dimT L i)) b ); let U:= Bulk G (dimT L i); constructor; · intro F k H; rw [Vexp]; exact hp.lap (pay b • U F) k ( (h.lap _ _ H).smul _ )
   intro F' H t h'; rw [ show ( _ ∘ F' )=( Lag ( G:=G ) L b i ) ∘ (pay b • ((Bulk G (dimT L i)) ∘ F')) from ?eq ]; swap; · funext t; exact Vexp _ -- ℂ ->Fun detail
   rw [Vexp]; apply hp.tip ; exact fun w=> ( h.tip _ _ _ h' w ).const_mul (pay b)
lemma GlA (b:Bool)(L:I→Side)(i:I)(v: I→Cover): Glance (Aspect (G:=G) b L i v):= by obtain he:= gl_A G (dimT L i) (v i); obtain hp:= gl_read (iota G (dimT L i)) b; exact ⟨ fun A k h=> hp.lap _ _ (he.lap _ _ h), fun A H v h=> hp.tip _ _ _ ( he.tip _ _ _ h )⟩
-- port shims
abbrev PayB (L:I→Side)(b:Bool)(i:I):= Tape (Scan (G:=G) b L i ) i
abbrev PayA (L:I→Side)(b:Bool)(i:I)(v:I→Cover):= Tape (Aspect (G:=G) b L i v) i
lemma pay_at (F:Glade G I)(t:ℝ): PayB L b i F t=Lag (G:=G) L b i ( pay b • Bulk G (dimT L i) ( F i t )):= Vexp _
lemma charge (F:Glade G I)(t:ℝ): PayA L b i v F t=Lag (G:=G) L b i ( anchor G (dimT L i) (v i) ( F i t ) ):= As_h _
abbrev RotateX (Z:Lin I) (P:Planet G I)(F:Glade G I):= adjust Z.orbit ( pay Z.orbit • term_birth P F )
local notation "Ω"=> enterV L b
local notation "δ"=> dimT L i
local notation "Γ"=> σbranch ( n:=dimT L i ) (G:=G)
include L
-- `include L` uses shadow? explicit.M.Rel
lemma pay_cycleB (b:Bool)(h:Toned F)(hp:Glow P): Static (zoneP L b P i) ( PayB L b i F )=PayB L b i ( CPlan (enterV L b) P F ) + ∑ z:Half, PayA L b i (loci (enterV L b) z) (RotateX (enterV L b) P F):= by
    funext t; simp only [Static, zoneP, primary, Finset.sum_apply,pay_at,charge,Pi.add_apply]; let K:= P i t; have he:= hp.proper i t; obtain ht:= h.sound i t; let S:= iota G δ; rw [ S.read_pc b (riverOK he.pin he.gov) _ ,map_smul]; cases b; · simp only [imageV,Bool.false_eq_true, ↓reduceIte]; rw [pc_bulk ht]; simp only [RotateX, adjust,enterV,Bool.false_eq_true,↓reduceIte, Pi.zero_apply, map_zero,Finset.sum_const_zero,add_zero ]; rfl -- pay coherence
    unfold imageV; rw [ if_pos rfl,Cascade,frame_add,LinearMap.add_apply, pc_bulk ht, show S.imageW (mat δ _)=faceκ true δ ( P i t ) from rfl, image_bulk (L i) ht he.pin ]; rw [ smul_add,map_add,Finset.smul_sum, map_sum ]; refine congr_arg₂ (· + ·) rfl ?_; refine Finset.sum_congr rfl fun z hz=>?_ -- likely term tactic
    change S.readerV true ((pay true) • anchor G δ _ _)=S.readerV true (anchor G δ (Tloc (L i) z) ((pay true) • birth (ηbone true (P i t)) (F i t))); rw [map_smul (anchor G δ (Tloc (L i) z))]
-- no time derivative.Links
end YM.MS.Orbit.LogReal
