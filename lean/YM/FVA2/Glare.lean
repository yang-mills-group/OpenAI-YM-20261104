import YM.FVA2.TokenFlow
/-!
# Smoothness of all rays. exp times power-log costs through transport; no assumed analytic.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.Taper
open Function Filter Set MeasureTheory Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Pic Forge Legacy
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Program MS.Book.Convolve Clock
open Hop
open scoped Topology ContDiff Classical
variable {G:Gauge} {F:Labels.Frames G} {d:ℕ} (s:ℝ)
section horizon
local notation "W'"=> Buffer F d
variable (D:Detector F d)(p:Buffer F d)
abbrev energy (s:ℝ): ℕ→ℝ:=factor s
abbrev Step : Module.End ℝ (Buffer F d):= Verne.Down F (energy (-s)) (energy s)
lemma Δsec (p: E F d): Δ F (-s) d (Δ F s d p)=p:= LinearMap.congr_fun (g:=LinearMap.id) ( by rw [ ← Verne.Δ_sum, neg_add_cancel, Verne.Δ_0 ] : Δ F (-s) d ∘ₗ Δ F s d =_ ) p
lemma sae : settled (settled (Øb F (-s) d,p),Øb F s d)=Step s p:= by apply frameC_i; rw [ frame_settled,frame_settled,frame_Øb,frame_Øb ]; apply LinearMap.ext; intro v; change Δ F (-s) d ( Δ F s d v + p.1 ( Δ F s d v ) )= v + Δ F (-s) d ( p.1 ( Δ F s d v ) ); rw [map_add,Δsec]
local infixr:70 " ◃ "=> luxury
lemma epoch (A: Word (Buffer F d)) : Step s ∘ A= ( just ( Øb F (-s) d ) ◃ A ) ◃ just (Øb F s d):= by
   funext n; let f:= delay A n; let L: Buffer F d →L[ℝ] Buffer F d := ( LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:= Buffer F d) (F':=Buffer F d) (Step (F:=F) (d:=d) s));
   have he:Act n f A:= Act.swell _ le_rfl;
   have hv:Act n (fun t=> L ( f t )) ( L ∘ A ):= by exact Act.linear (E:=Buffer F d) ( G:=Buffer F d) (L:=L) he; -- near
   have hm : Act n (fun t=> settled ( settled (Øb F (-s) d,f t),Øb F s d )) (( just ( Øb F (-s) d ) ◃ A ) ◃ just (Øb F s d)):= ((((Act.static ( n:=n ) _).zipper he).transit (m:=settled) settled_diff.contDiffAt).zipper ( Act.static _ )).transit (m:=settled) settled_diff.contDiffAt;
   simp_rw [sae ] at hm; exact hv.trans_at hm le_rfl
private def spy : W'→ₗ[ℝ] (BasisIx G d → BasisIx G d →ℂ) where
   toFun p i j:= (sameAxis F d).coord j ( bufferL F p (sameAxis F d i))
   map_add' a b:= funext fun i=>funext fun j=> map_add ((sameAxis F d).coord j) (bufferL F a (sameAxis F d i)) (bufferL F b (sameAxis F d i))
   map_smul' r a:= funext fun i=>funext fun j=> LinearMap.map_smul_of_tower (( sameAxis F d ).coord j) r (bufferL F a (( sameAxis F d ) i))
private lemma informed : Function.Injective (spy ( F:=F ) (d:=d)) := by
   intro i j h; apply follows_right; apply ( sameAxis F d ).ext; intro k; apply ( sameAxis F d ).repr.injective; ext l; exact congr_fun (congr_fun h k) l
lemma spy_price (i j: BasisIx G d) : spy (Step s p) i j=( ( Verne.factor ( -s ) j.size:ℂ )* ( Verne.factor s i.size:ℂ )) * spy p i j:= Verne.reprφ ..
private lemma cf {V W: Type*} [NormedAddCommGroup V][NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W][FiniteDimensional ℝ V] (f: V →ₗ[ℝ] W): ContDiff ℝ ω f := f.toContinuousLinearMap.contDiff
private lemma continuous_left {V W:Type*}[NormedAddCommGroup V][NormedAddCommGroup W] [NormedSpace ℝ V][NormedSpace ℝ W][FiniteDimensional ℝ V][FiniteDimensional ℝ W] (L: V→ₗ[ℝ] W)(f:ℝ→V)(h:Injective L)(hp:ContDiff ℝ ω (L ∘ f)): ContDiff ℝ ω f:= by
    have hK (t:ℝ):= LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr h) (f t); convert ((cf L.leftInverse).comp hp) using 1; exact funext fun t=>(hK t).symm
lemma glow (g:ℝ→ Buffer F d)(h:ContDiff ℝ ω g): ContDiff ℝ ω (fun t=> Step t (g t)):= by
    let T (v:ℝ):= Step v (g v); let C:= BasisIx G d→BasisIx G d→ℂ;
    have he:ContDiff ℝ ω (spy ∘ T):= by
        apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j; unfold T;
        simp_rw [Function.comp_apply, spy_price ]; apply ContDiff.mul; · unfold Verne.factor; apply ContDiff.mul; exact ( Complex.ofRealCLM.contDiff.comp (f:=fun (x:ℝ)=> Real.exp (-(j.size:ℝ)* -x )) (by fun_prop) ); exact Complex.ofRealCLM.contDiff.comp (f:=fun (x:ℝ)=> Real.exp ( -(i.size:ℝ)*x )) (by fun_prop)
        exact contDiff_pi.mp ( contDiff_pi.mp ((cf ( V:=Buffer F d ) spy).comp h) i ) j -- h
    exact continuous_left ( V:=Buffer F d ) ( W:=BasisIx G d→BasisIx G d→ℂ ) spy T informed he
lemma solar (h:withinBlock F p=p) : Step s p=p:= by
   apply informed; funext i j; rw [spy_price]; by_cases hi:i.size=j.size; · rw [ hi, ← Complex.ofReal_mul, Verne.factσ ]; simp [Verne.factor ]
   rw [show spy p i j=0 from (recognized F p).1 h _ _ hi,mul_zero ]
end horizon
lemma reflectStep (v: Strat F)(d:ℕ) : ( Λ F (-s) * v * Λ F s ).wire d= Step s ∘ v.wire d:= (epoch s (v.wire d)).symm
lemma beam (A: Hop F) (h:A.gradedStep) : glance s A=A:= Hop.ext rfl (Strat.ext fun i=> by change wire ( Λ F (-s)* A.Z*Λ F s ) i= A.Z.wire i; rw [reflectStep ]; exact funext fun k=> solar s ( A.Z.wire i k ) ( congr_fun ( congr_arg (fun p:Strat F=>p.wire i) (show only A.Z=_ from h)) k ))
section smooth
variable {W Z:Type*}[NormedAddCommGroup W][NormedSpace ℝ W][NormedAddCommGroup Z][NormedSpace ℝ Z]
   (u:ℝ→ Word W)
def soft (f:ℝ→Word W) := ∀ i,ContDiff ℝ ω (fun t=>f t i)
variable (hu:soft u)
include hu
lemma softer (f:W→Z) {p:W} (hc:ContDiffAt ℝ ω f p)(hh:∀ t,u t 0=p): soft fun t=> run f (u t):= by -- same as progress.Real proof via faa
   intro i; let F(t:ℝ):= delay (u t) i; let v(t:OrderedFinpartition i):= iteratedFDeriv ℝ t.length f p; let z(s:ℝ)(b:OrderedFinpartition i)(j:Fin b.length):=( (b.partSize j).factorial:ℝ) • u s (b.partSize j); let φ:ℝ:=( i.factorial:ℝ )⁻¹;
   have hp(s:ℝ): run f (u s) i= φ • ∑ t:OrderedFinpartition i,v t (z s t):= by have hf:Act i ( F s ) ( u s ):= Act.swell _ le_rfl; unfold run; change someJ (f ∘ F s) i= _; unfold someJ; rw [ iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hf.zero.symm ▸ (hh s).symm ▸ hc) hf.nice le_top, hf.zero,hh ]; simp_rw [hf.actual _ ( OrderedFinpartition.partSize_le _ _ ) ]; rfl
   simp_rw [hp]; exact contDiff_const.smul ( ContDiff.sum ( fun t _=> ( v t ).contDiff.comp ( f:=fun s=> z s t ) ( contDiff_pi.mpr fun j=> contDiff_const.smul ( hu _ )) ) ) -- ContDiff ω? CML.contDiff uses ∞ maybe hooks
lemma relay_u (f:ℝ→ Word ℝ)(h:soft f) : soft (fun i:ℝ=> ren (f i) ( u i )):= by intro k; unfold Jet.ren Jet.order; refine contDiff_const.smul ( ContDiff.sum (fun t _=>?_)); exact ( contDiff_prod (fun j _=> contDiff_const.mul ( h ( t.partSize j ))) ).smul ( contDiff_const.smul ( hu t.length ) )
end smooth
variable {u v:ℝ→ Word (Buffer F d)} (p q:ℝ→Hop F)
lemma gear (h:soft u)(H:soft v)(hv:∀t:ℝ,Stable ( u t ))(hp:∀t:ℝ,Stable ( v t )): soft (fun t=> luxury ( u t ) ( v t )):= softer (fun t=> Jet.pair (u t) (v t)) ( fun i=> ContDiff.prodMk ( h i ) ( H i ) ) _ settled_diff.contDiffAt (p:= ( (0,0) : Buffer F d× Buffer F d )) (fun i=>Prod.ext ( hv i ) ( hp i ) )
-- α external geometry smooth.*.
def glowT : Prop:= (∀ d,soft (fun t=> (p t).Z.wire d)) ∧ soft (fun t=>( p t ).f)
lemma habitT (h:Legacy.habit p): glowT p:=⟨ fun d i=> smooth_eval _ ( h.1 d i ),fun i=> smooth_eval _ ( h.2 i )⟩
lemma glow_mul (h:glowT p)(hp:glowT q): glowT (fun t=> p t*q t ):= by
    unfold glowT; simp_rw [walkF,walkZ,pay,resume_wire ]; exact ⟨fun d=> gear ( relay_u _ (h.1 d) _ hp.2 ) (hp.1 d) (fun t=> Verne.fast _ ((p t).tangent _) (q t).rooted) (fun t=> (q t).tangent d ), relay_u _ h.2 _ hp.2 ⟩
lemma glow_gl (h:glowT p): glowT (fun t=>glance t (p t)):= by
    refine ⟨ fun d=> ?_,h.2 ⟩; intro i; unfold glance; simp only []; simp_rw [ reflectStep, Function.comp_apply ]; exact glow _ ( h.1 d i )
variable {O:Booked (wings G)} {h:G.Simple} (V:Warehouse G)(M:MS_Data G O){t:ℝ}(R:Booth t V.F)(Sx:Pic.pass V h M R)
lemma fixstep (v:ℝ) : habit (fun s=> Forge.cflow V M R s v Sx):= by
    have hu:= debut_m V h M R Sx v; let P:= Forge.transfer V M R v Sx;
    unfold Forge.cflow slideOf; simp_rw [beam _ ( A:= Forge.transfer V M R v Sx ) (Forge.gradedT V M R v Sx) ]; exact habit_mul ( habit_mul ( constantV _ ) hu ) ( constantV _ )
lemma trajectory (v:ℝ) : glowT (fun t=> Forge.xflow V M R t v Sx):= by
    let L(t):= Forge.diffuse V M R t v Sx; let P:= Forge.Pay V M R Sx v; have hL:= habitT L ( debut_m V h M R Sx v ); have he:= glow_gl _ ( habitT ( fun _:ℝ=>P) (constantV P) ); exact glow_mul _ _ ( glow_mul _ _ ( habitT _ (constantV _) ) hL ) he
end YM.FVA2.Taper
