import YM.FVA2.Smooth.Blades
/-!
# Pointwise derivative conclusions on MS `book` and `tour`

Includes formal connected and all-subset full versions. No lattice comparisons here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
variable [LinearOrder W][Fintype W]
open MS.Tide
open MS.Momentum
variable (S:MS_Data G M) (u:W→Rake.Label b)
-- compute on Board specialized Draw W.
local notation "Π"=> Draw W
local notation "μ₀"=> (fun (_:Draw W)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G (Draw W) (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
variable {v r t:ℝ} {s: Steps W}
local notation "R"=> frameF (Draw W) v
local notation "Ω"=> approach R S
variable {x: Position W (Draw W)} {T T' U:Finset W} {ρ:Steps W} {J: Set (Draw W)} {q: Draw W}
variable {V:Steps W→Dance G (Draw W) W} {w:Legs (Lane4 G)} {A:Type}
open MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Fleet -- inspect
-- step-zero agreement. H and Book literal on support distinct.
def plain (_v:W): List Axis:= []
omit [Fintype W] in
lemma unmarkedR (S:MS_Data G M)(x: Position W I)(u:W→Rake.Label b)(V: Dance G I W): DOrd M P S u x V↔ charted P S u plain x V:= by rfl
omit [LinearOrder W] in
lemma clamp (p:Draw W) : IsOpen (setOf (Clamp p)):= by
 unfold Clamp; simp only [ Set.setOf_forall ]; refine isOpen_iInter_of_finite (fun i=> isOpen_iInter_of_finite (fun j=> isOpen_iInter_of_finite (fun t=>?_))); let f(x:Draw W):=‖x i-x j‖; have hf: Continuous f:= by unfold f; fun_prop
 exact (isOpen_lt (g:=f) continuous_const hf).inter (isOpen_lt hf continuous_const)
lemma localK (T:Finset W)(n:ℕ)(p:Draw W)(h:Injective p): ContDiffOn ℝ ∞ (fun q=> book S u v q T n) (setOf (Clamp p)) := by
    let Wt := fun w=> Window w p; let F:= curve R S u Wt; let J:= (setOf ( Clamp p )); have hh(y:Draw W)(he:y∈J)(t:W): Wt t y=y t:= if_pos he
    have hx:= Dial.turnH h v; have hv (s:Steps W): charted R S u s Wt ( F s ):= arrived S u s _ hx; refine ContDiffOn.congr (smoothness S u (r:=1) (clamp p) (x:=Wt) (fun i y hy=> (hh y hy i).trans (one_smul ..).symm ) hx hv T n plain) ?_; intro q hq; let Z:=F plain; have he : pointI Wt q=q:= funext ( hh q hq ); rw [← he]; -- careful RHS q rewritten too
    -- rewrite only lhs.
    obtain hp:= Point_t S u v ( x:=Wt ) hx ( ( unmarkedR _ _ _ _ ).2 ( hv plain ) ) q T n; rw [he] at hp; rw [ he ]; exact hp.symm
lemma pass_b (p:Draw W)(h:Injective p)(T:Finset W)(n:ℕ): ContDiffAt ℝ ∞ (fun q=> book S u v q T n) p:= (localK S u T n p h).contDiffAt (earlyW h)
-- full via bouquet combinatorial recurrence
namespace Flowers
variable {f g: Draw W→ Finset W→Book.Convolve.T ℂ} 
abbrev Rich (f:Draw W→Finset W→Book.Convolve.T ℂ)(p:Draw W):Prop:= ∀ i j, ContDiffAt ℝ ∞ (fun v=>f v i j) p
open MS.Puff.Actors MS.Puff.SplitP -- subs ns
lemma multiply (hF:Rich f q)(hx: Rich g q) : let P:= (Trunk.stack (marked W)).core; Rich (fun i=> P ( f i ) ( g i )) q := by
    intro P i j; change ContDiffAt ℝ ∞ (fun p=>( ∑ d∈ subs i,Trunk.core ( f p d.1 ) ( g p d.2 )) j) q; simp_rw [Finset.sum_apply]; -- apply ContDiffAt.sum ... type by function
    refine ContDiffAt.sum fun d _=>?_ ; change ContDiffAt ℝ ∞ (fun p=>∑ x∈ Finset.antidiagonal j,f p d.1 x.1 * g p d.2 x.2) q; exact ContDiffAt.sum (fun i hi=> (hF _ _).mul (hx _ _) )
lemma awaits (hf:Rich f q)(k:ℕ) : let P:= Trunk.stack (marked W); Rich (fun i=> P.power (f i) k) q := by induction k with| zero=>intro P i j; exact contDiffAt_const| succ k ih=> exact multiply hf ih
lemma whole (hf:Rich f q)(i:Finset W)(j:ℕ): ContDiffAt ℝ ∞ (fun p=> Puff.Mom.bouquet (f p) i j) q:= by
    unfold bouquet Cheer cheers; simp_rw [ Finset.sum_apply ]; apply ContDiffAt.sum; intro x hx; exact ( awaits hf x i j ).const_smul (Actors.phase x) -- bound binder namespace
end Flowers
lemma passes (v:ℝ)(p:Draw W)(h:Injective p)(T:Finset W)(n:ℕ): ContDiffAt ℝ ∞ ( fun q=> tour S u v q T n ) p:= Flowers.whole ( f:= fun q:Draw W=> book S u v q ) ( pass_b S u p h ) T n
end YM.FVA2.Smooth.Cruise
