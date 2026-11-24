import YM.MSbar.Dim.Trace
import YM.MSbar.Transfer.Layer
/-! Temperate test plots with shared support tags. Avoid introducing declarationally analytic
functions on noninteger vector domains; need actual analytic operations, via real orthogonal
embeddings & dimensional calculus. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Function Set Filter Symbol Dim Transfer
open scoped Topology BigOperators Classical ContDiff
structure Site (X:ℕ→Type) extends Motion X where
    plot {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m:ℕ} : (E → X m) → Prop
    views {m : ℕ} {E D:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
         {x:E→ X m} : plot x → ∀ {p:D→E}, p.HasTemperateGrowth → plot (x ∘ p)
    size_up {m n : ℕ}(V : Move m n) {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x:E→X m} : plot x → plot (move V ∘ x)
variable {X Y W : ℕ→Type} {S:Site X} {K : Site Y} {m n j : ℕ}
variable {F : ∀ m,X m→ℂ}
namespace Site
def prod (S:Site X)(K:Site Y): Site (fun m=> X m × Y m):= {
    toMotion := Motion.prod S.toMotion K.toMotion
    plot := fun p => S.plot (Prod.fst ∘ p) ∧ K.plot (Prod.snd ∘ p)
    views := fun h => by intros p hp; exact ⟨S.views h.1 hp,K.views h.2 hp⟩ -- strict impl
    size_up := fun V => by intro E i1 i2 i3 x h; exact ⟨S.size_up V h.1,K.size_up V h.2⟩ }
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

def simple : Site (fun _=>E):=
 { toMotion := constMotion E
   plot := fun p=>p.HasTemperateGrowth
   views := fun h => by intros p hp; exact h.comp hp
   size_up := fun V => by intro E' i1 i2 i3 x h; exact h }
def moving : Site Hat := {
    toMotion:= Dim.vectors
    plot:=fun p=>p.HasTemperateGrowth
    views := fun h => by intros p hp; exact h.comp hp
    size_up:= fun V => by intro E i1 i2 i3 x h; exact V.toContinuousLinearMap.hasTemperateGrowth.comp h }
end Site
variable {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

-- allow high halfplane costs only needed on the whole plane regime.
structure Bet (U:Set ℂ) (j:ℕ)(F:ℂ×E→ℂ) : Prop where
   cost : Symbol.AH U F
   gains : U=univ → Transfer.Market j F
variable {U : Set ℂ} {f g : ℂ × E → ℂ}
namespace Bet
lemma add (hf:Bet U m f)(hg:Bet U m g): Bet U m (f+g):= ⟨hf.cost.add hg.cost, fun h=> (hf.gains h).add (hg.gains h)⟩
lemma neg (hf:Bet U m f): Bet U m (-f):= ⟨hf.cost.neg,fun h=> (hf.gains h).neg⟩
lemma sub (hf:Bet U m f) (hg:Bet U m g): Bet U m (f-g):=by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma mul (hf:Bet U m f)(hg:Bet U n g): Bet U (m+n) (f*g):= ⟨hf.cost.mul hg.cost,fun h=> (hf.gains h).mul (hg.gains h)⟩
lemma static {f:E→ℂ}(hf: f.HasTemperateGrowth): Bet U 0 (fun x:ℂ × E => f x.2):= ⟨AH.param_tame hf,fun _=> Market.no_z hf.1.continuous⟩
lemma cte (c:ℂ): Bet U 0 (fun _ : ℂ×E=>c):= static (HasTemperateGrowth.const c)
lemma scale (c:ℂ)(hf:Bet U m f): Bet U m (c • f):= by simpa only [zero_add] using! (cte c).mul hf
lemma const_scale (c:ℂ)(hf:Bet U m f): Bet U m (fun x=>c * f x):= hf.scale c
lemma zero : Bet U m (0 : ℂ×E→ℂ):= ⟨AH.constant 0,fun _=>Market.zero⟩
lemma sum {ι:Type} {f:ι→ℂ×E→ℂ} (s:Finset ι) (H:∀ i∈s,Bet U m (f i)): Bet U m (∑ i∈s,f i):=⟨AH.sum fun i hi=> (H i hi).cost,fun h=> Market.sum fun i hi=> (H i hi).gains h⟩
lemma sum_e {ι:Type} {f:ι→ℂ×E→ℂ} (s:Finset ι) (H:∀ i∈s,Bet U m (f i)): Bet U m (fun x=> ∑ i∈s,f i x):= by simpa only [← Finset.sum_apply] using sum s H
lemma identity : Bet U 0 (fun x:ℂ×E=>x.1):=⟨⟨fun _ _=>⟨Prod.fst, tame_projL, EventuallyEq.rfl⟩,fun _ _ _=> differentiableAt_id⟩,fun _=> Market.z_self⟩
lemma route (hf:Bet U m f){p:D→E}(hp:p.HasTemperateGrowth): Bet U m (fun x:ℂ ×D=> f (x.1,p x.2)):= ⟨hf.cost.arguments hp,fun h=> Market.comp (hf.gains h) hp.1.continuous⟩
lemma congr (hf:Bet U m f)(hu : IsOpen U)(H:∀ z∈U,∀ x,f (z,x)=g (z,x)): Bet U m g:= by
   refine ⟨hf.cost.congr hu H,fun h=>?_⟩;rw [show g=f from funext (fun x=> (H x.1 (h ▸ mem_univ _) x.2).symm)]; exact hf.gains h
lemma upon (hf:Bet U m f){V:Set ℂ}(h:V⊆U): Bet V m f:= ⟨hf.cost.upon h,fun H=> hf.gains (eq_univ_of_univ_subset (H ▸ h))⟩
lemma ignore (hf:Bet U m f)(he:U≠univ)(k:ℕ): Bet U k f:= ⟨hf.cost,fun h=>(he h).elim⟩
end Bet

-- Curvature character of functional values. Supports plot evolution.
abbrev Record (T:ℕ→Type):= ℂ→∀ m,T m→ℂ
structure Eligible (U:Set ℂ) (j:ℕ)(S: Site X)(f:Record X):Prop where
    natural (z : ℂ) : z ∈ U→S.toMotion.Natural (f z)
    ev (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m:ℕ}(x:E→X m) : S.plot x → Bet U j (fun p:ℂ×E=> f p.1 m (x p.2))
end YM.MSbar.Domain
