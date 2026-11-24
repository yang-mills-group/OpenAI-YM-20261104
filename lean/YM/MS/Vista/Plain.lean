import YM.MS.Vista.Sol
/-!
# Progress in τ=log(1+R) relative heat scale.Plan work. Monotone transfer from boundary.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve
open High Orbit -- Cog after? declared via Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{P:Belt I}{b c:Bool} {X F H U:Glade G I}{r:ℕ}{A:P.time→ℝ}{T:Scale I}{a:I→ℝ}
-- Progress.c optionally positives. monotone assumed only per w. Lens threshold sheets. use for diff.
abbrev Adjuster (P:Belt I)(b c:Bool)(A:P.time→ℝ): Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ w: Wire (BH G) E QP, Course b w→ fig c w.length→ monoY P (Qbud w P.price A)
lemma kernel (h:Accel P a)(hp:LookS F H)(hf: Adjuster ( G:=G ) P b c A)(hv:nn A)(ht: Lease b c P.price ( LaunchF P a F ) A)(he:∀ r:ℕ,fig c r→ coinF b P F A (r+2) → coinF b P H A r) : Here b c P F A := by
    obtain ⟨M,hM⟩:= aboveC P b hp.modal.cap; apply poses; suffices hx: ∀ k:ℕ,∀ r:ℕ,M≤ r+k→fig c r→coinF b P F A r from fun x=> hx M x (by omega); intro k; induction k using Nat.strong_induction_on with| h k ih=>
       have hz (r:ℕ)(hr:M<r)(hf:fig c r): coinF b P F A r:= reaches ( pinch (Lease.zero (G:=G) (b:=b) (S:=P.price) hv) hf ) (fun i w hW ht=> hM i w hW (ht ▸ hr)) -- rewrite orientation
       intro v hx hs; by_cases hm:M<v; · exact hz v hm hs
       have hB : coinF b P F A (v+2):= by
          by_cases hl:M<v+2; · exact hz (v+2) hl (fun _=>by omega)
          exact ih (k-1) (by omega) (v+2) (by omega) (fun h=>by omega)
       intro E _ _ w hw hW; obtain hu: fig c ( w.length ):= hw ▸ hs; exact slowC hp h (hf E w hW hu ) hv (he v hs hB E w hw hW) (ht E w hW hu)
-- height-shift ep.Time.K.Arithmetic. lamp λ.Energy.
abbrev τ (x:ℝ):= Real.exp x-1
noncomputable def up (P:Glade G I): Glade G I:= fun i t=> P i (τ t)
def warp0 (G:Gauge)(I:Type): Glade G I→ₗ[ℂ] Glade G I:={ toFun:= up, map_add' _ _:=rfl,map_smul' _ _:=rfl }
def bend (G:Gauge)(I:Type): Glade G I→ₗ[ℂ] Glade G I:={
    toFun F:= fun i t=> (( exp t :ℝ):ℂ) • up F i t
    map_add' a b:= by funext i t; exact smul_add ( (Real.exp t:ℝ):ℂ ) _ _ -- ext rank? choose
    map_smul' a b:= by ext; apply mul_left_comm }
abbrev lamp (x:ℝ): ℝ:=max 1 (τ x)
lemma τ_sm : ContDiff ℝ ∞ τ:= contDiff_exp.sub contDiff_const
lemma τ_D (y:ℝ): HasDerivAt τ ( exp y ) y:=(Real.hasDerivAt_exp _).sub_const _
lemma clock_m  (w:P.time): lamp (tstart w)≥1:= le_max_left .. -- linter
lemma turn_T (h:Toned F): Toned (warp0 G I F):= ⟨ fun i=> fun E _ _ f w hw he=> (h.touch i) E (τ ∘ f) w hw (τ_sm.comp he), fun i t=>h.sound i (τ t) ⟩
lemma turn_d (h:Toned F): Toned (bend G I F):= by
    obtain ht:= turn_T h; refine ⟨ fun i=>fun E _ _ f w hW he=>?_, fun i t=> speak_smul ( h.sound i (τ t) ) _ ⟩; exact ContDiff.smul (Complex.ofRealCLM.contDiff.comp (contDiff_exp.comp he)) ( ht.touch i E f w hW he )
lemma hooked (h:Toned F)(hv:Toned H)(hm: Modal F H): LookS (warp0 G I F) (bend G I H):= by
    refine ⟨ ⟨ by obtain ⟨i,hi⟩:=hm.cap; exact ⟨i,fun i t=> hi i ( τ t ) ⟩,fun i t w=>?_ ⟩, ( turn_T h ).touch, ( turn_d hv ).touch ⟩; exact (hm.pace i (τ t) w).scomp t (τ_D t)
lemma look_sub (hx:LookS F H)(hp: LookS X U): LookS ( F-X ) ( H-U ):= by
    refine ⟨ ⟨ ?_, fun i t w=> (hx.modal.pace i t w).sub ( hp.modal.pace i t w )⟩,fun i=>Tneg (hx.act i) (hp.act i),fun i=> Tneg (hx.der i) (hp.der i) ⟩; obtain ⟨r,hr⟩:=hx.modal.cap; obtain ⟨v,hv⟩:=hp.modal.cap; exact ⟨r+v, fun i t=> ( hr i t |>.up (by omega) ).sub ( hv i t |>.up (by omega))⟩
where Tneg {F H:Wind.Flow G}(hf:TouchF F)(he:TouchF H):TouchF ( F-H ):= fun E _ _ f w hw ht=> ( hf E f w hw ht).sub (he E f w hw ht)
end YM.MS.Vista
