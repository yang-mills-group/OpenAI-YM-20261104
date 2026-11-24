import YM.FVA2.Gen.Fires
import YM.FVA2.Gen.Flat
/-!
 # Transport on real continuous parameter-smooth paths
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set MeasureTheory Filter Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{R:Type}[NormedRing R][NormedAlgebra ℝ R][CompleteSpace R]
variable {F H : E×ℝ→R}{p q:E→ℝ→R}{x:E}
def Engage (x:E)(F:E×ℝ→R)(p:E→ℝ→R): Prop:= ContDiff ℝ ∞ F ∧ (∀ t:ℝ, F (x,t)=0) ∧ (∀ v:E,p v 0=1) ∧ ∀ (v:E)(t:ℝ),HasDerivAt ( p v ) ( p v t* F (v,t) ) t
local notation "R₁"=> unitInterval
variable (F) (h:Engage x F p)
include h
private def Licks : E→ C(unitInterval,R):= packing (Subtype.val (p:= fun a:ℝ=>a∈unitInterval)) continuous_subtype_val F h.1.continuous
omit [CompleteSpace R] in
private lemma licks_s (t:E)(i:R₁): Licks F h t i=F (t,(i:ℝ)):=rfl
variable {F}
omit [CompleteSpace R] in
private lemma licksC : ContDiff ℝ ∞ (Licks F h):= packages _ _ _ h.1
omit [CompleteSpace R] in
private lemma licks0 : Licks F h x=0:= ContinuousMap.ext (fun i=>h.2.1 (i.val))
private lemma Engage.views: (fun t=> p t 1) =ᶠ[𝓝 x] ( endpoint R ∘ Licks F h ):= ( at_actual (( licksC h ).continuous.continuousAt) _ h.1.continuous h.2.2.1 h.2.2.2 ( licks_s F h ) ( licks0 h ) ).symm
lemma Engage.smooth: ContDiffAt ℝ ∞ (fun t=> p t 1) x:= ( ( show ContDiffAt ℝ ∞ _ (Licks F h x) from by rw [ licks0 h ]; exact touchEnd R ).comp x ( licksC h|>.contDiffAt ) ).congr_of_eventuallyEq h.views
lemma Engage.base : p x 1=1:= by rw [show p x 1=endpoint R ( Licks F h x ) from h.views.self_of_nhds,licks0 h]; unfold endpoint; rw [ engine0 ]; rfl
omit h
section
variable {F H:ℝ×ℝ→ R}{p q:ℝ→ℝ→R}{n k :ℕ}(w:Engage 0 F p)(l:Engage 0 H q)(hl:∀ v:ℝ,Near n (fun t=> F (t,v)) (fun t=> H (t,v)))
include w
omit [CompleteSpace R] in
private lemma iter_licks (n:ℕ)(i:R₁): iteratedDeriv n (Licks _ w) 0 i= iteratedDeriv n (fun t:ℝ=> F (t,i)) 0:= by
    let L:= ContinuousMap.evalCLM ℝ (M:=R) i; change L _ = _; rw [ ← iterL n ( ( licksC w ).contDiffAt ) ]; rfl
include l hl
omit [CompleteSpace R] in
private lemma Licks.near : Near n ( Licks _ w ) ( Licks _ l ):= fun i hi=> ContinuousMap.ext fun t=> ( iter_licks w i t ).trans ( ( hl t i hi ).trans ( iter_licks l i t ).symm )
lemma Engage.near: Near n (fun t=> p t 1) (fun t=> q t 1):= (near_of_ev w.views).across ( ( Near.vcomp ( Licks.near w l hl ) ( licksC w|>.contDiffAt ) ( licksC l|>.contDiffAt ) ( by rw [ licks0 w ]; exact touchEnd R ) ).across ( near_of_ev l.views.symm ) )
lemma Engage.one_more:
    iteratedDeriv (n+1) (fun t=> p t 1) 0-iteratedDeriv (n+1) (fun t=> q t 1) 0= ∫ i in (0:ℝ)..1, iteratedDeriv (n+1) (fun t:ℝ=> F (t,i)) 0- iteratedDeriv (n+1) (fun t:ℝ=> H (t,i)) 0:= by
    rw [ w.views.iteratedDeriv_eq (n+1),l.views.iteratedDeriv_eq (n+1), Gen.ahead ( Licks.near w l hl ) ( licksC w|>.contDiffAt ) ( licksC l|>.contDiffAt ) ( show ContDiffAt ℝ ∞ (endpoint R) (Licks F w 0) from by rw [ licks0 w ]; exact touchEnd R ), licks0 w,engine_deriv ]
    refine intervalIntegral.integral_congr fun s hs=> ?_; let t:= projIcc (0:ℝ) 1 zero_le_one s; have he : (t:ℝ)=s:= by exact congrArg Subtype.val ( projIcc_of_mem (zero_le_one) ( show s ∈ Icc 0 1 by simpa [uIcc_of_le] using hs ) )
    change iteratedDeriv (n+1) (Licks F w) 0 t-iteratedDeriv (n+1) (Licks H l) 0 t=_; rw [ iter_licks w,iter_licks l, he ]
omit l hl
lemma Engage.initial_slope: deriv (fun t=> p t 1) 0= ∫ i in (0:ℝ)..1, deriv (fun t:ℝ=> F (t,i)) 0 := by
    let Z:=fun _:ℝ×ℝ=> (0:R); let Q:=fun (_ _:ℝ)=>(1:R); have h':Engage 0 Z Q:= ⟨contDiff_const,fun _=>rfl,fun _=>rfl,fun z t=>by simp only [Z,mul_zero]; exact hasDerivAt_const .. ⟩; obtain he:= w.one_more h' (n:=0) (fun v=> near_first.mpr (w.2.1 v)); simpa only [iteratedDeriv_one,Z,Q,deriv_const',Pi.zero_apply,sub_zero,Nat.zero_add] using he
end
end
-- Applied to real paths. preserve Mat norm choice from Gauge.
open Lattice RG Wilson Precision Set Function Filter MeasureTheory Labels Source
variable {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}
local notation "Cℓ"=> G.Color
local notation "H₀"=> G.El
local notation "M"=> G.Mat
variable {p:E×ℝ→G.Color}{q:E→ℝ→G.El}
def Meets (p:E×ℝ→G.Color)(q:E→ℝ→G.El): Prop:= ∀ x:E, SolvesLink (q x) (fun t:ℝ=> p (x,t))
def enter (G:Gauge) (F:E×ℝ→ G.Color) (x:E×ℝ) := G.colorMat ( F x )
lemma Meets.equip (hp:ContDiff ℝ ∞ p)(hx:∀ t:ℝ,p (x,t)=0)(u: Meets p q): Engage x (enter G p) ( fun x t=> G.mat (q x t) ):= by
    refine ⟨( G.colorMat.toContinuousLinearMap.contDiff.comp ( hp ) ),fun t=>?_,fun x=>by change G.mat (q x 0)=_; rw [(u x).1]; exact G.mat_one, ?_ ⟩; · simp only [enter,hx,map_zero]
    intro v; exact ( u v ).2
-- notation (simp)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma meets_unique (h:Meets p q){q':E→ℝ→ G.El}(u:Meets p q'): q=q':= by funext a t; exact Hol.agree isOpen_univ convex_univ (Set.mem_univ _) (A:=fun x:ℝ=>p (a,x)) (fun y _=> ( h a ).2 y) (fun y _=> ( u a ).2 y) ( Eq.trans ( h a|>.1 ) ( u a|>.1 ).symm ) (Set.mem_univ t)
lemma meets_real (hp:ContDiff ℝ ∞ p): ∃ q,Meets p q:= by choose Q h using fun x:E=> @Hol.pipes G (fun t:ℝ=> p (x,t)) ( hp.comp (f:=fun t:ℝ=>(x,t)) (contDiff_const.prodMk contDiff_id) |>.of_le (by exact_mod_cast WithTop.coe_le_coe.mpr le_top) ); exact ⟨Q,h⟩
end YM.FVA2.Gen
