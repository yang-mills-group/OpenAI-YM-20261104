import YM.FVA2.Extras.Proj
import YM.MS.Milk.Fall
/-! # Check on higher order starting when specialization vanishes

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I:Type}{G:Gauge}{b d:ℤ}{r k n:ℕ}{B:Deck G}{K:Booked B}{M:MS_Data G K}
open Alps Garment Milk Tone.Frame MS.Hem.Mell Awning Book MS.Arts Dock MS.Motif Local.Physical
variable {U : T ( Arts.Mob G )}{X:Blue G}{Q:CostsM G}{h:ℕ}{a t:ℝ}
variable (H:comet h 0 M.bulk ( gloss U ) X Q)(hT:Badge false ( gloss U 0 ) h 0)
variable (hm:Goods (k:ℤ) (U 0)) (h0: U 0 0=0)
lemma dawn (f:ℝ→ℂ)(p q:ℤ)(h:p≤q-1)(hh:f∈ Bowl p)(hf: Plane.Shape f q): f=0:= by
    rcases lt_or_ge q 0 with h1|h1; exact hf.charge h1;
    have hp:= Milk.tarnα hh 0 1 (g:=-q) (by omega); simp only [Polynomial.eval_one,one_mul] at hp
    have H(t:ℝ): f t=t^q • f 1:= by simpa only [ smul_eq_mul,mul_one ] using hf.scale t 1
    have ht:= H; rw [ funext (fun i:ℝ=> (by rw [H (exp i),Drops.pale,smul_smul,← zpow_add₀ ( exp_pos i ).ne',neg_add_cancel,zpow_zero,one_smul] : Drops.pale (-q) i • f (exp i)=f 1 )) ] at hp; funext t; rw [H,tendsto_nhds_unique tendsto_const_nhds hp,smul_zero]; rfl
include H hT hm h0
lemma limiter : Limit (letIn h (logMass a) X 0 () t) (k-2:ℤ) := by
    obtain ht:= (HM H hT (r:=k) (s:=t) (y:=logMass a ()) (fun n l hl=> hm n l (by rw [mod_int]; omega))) 0; change Limit (letIn h (logMass a) X 0 () t-U 0 0) _ at ht; simpa only [h0, sub_zero] using ht
omit h0 in
lemma lighter (j:ℕ)(hs:j<k)(hp:First ( letIn h (logMass a) X ) a h 0 j ): Narrow (letIn h (logMass a) X) 0 j 0=0 := by
    let F:=Narrow (letIn h (logMass a) X) 0 j 0; have hx:= ( lease_one.mp ( hp.form ( Response.mark H ) ) ).2.1
    ext l; by_cases he:l.length=j; swap; · exact strange _ (by omega)
    let W:= hereZ h (X 0) 0 a; have hC: Caper ((h:ℤ)-k) W:= by
       obtain C:= give (K:=U 0) hT; let q:ℤ:= (h:ℤ)-k; have hQ:= Standard C.1 C.2.1 hm; obtain hu:= RootF (H 0); exact valueC hu.toll hu.wet _ (Needed _) (Run0 H hT (Eventually.of_forall (fun i:ℂ=>hQ))) -- pressure.L.P.
    let v:= ray l; let N:=fieldVal F v; have hu:N∈Bowl ( PriceR (m:=0) ((h:ℤ)-k) v ):= by
        obtain hr:= hC 0 ℝ v 0 1; simp only [smul_eq_mul,mul_one,zero_add] at hr; rwa [show (fun t:ℝ=> W 0 ( sail v t ))=N from funext fun p=> (enough ( sail v p ) (by unfold v; rw [ sail_len,ray_len,he ]) ).symm ] at hr
    have hW:N=0:= dawn N _ _ (by unfold PriceR mass; have hv : v.length=l.length:= ray_len _; omega) hu (hx ℝ v (fun i=>Bool.noConfusion i)); obtain h':= congr_fun hW (1:ℝ); simpa [ v,N,fieldVal ] using! h'
lemma clean_zero (a:ℝ) : letIn h (logMass a) X 0=0:= by
    let Z:= letIn h (logMass a) X
    have Hk(j:ℕ)(he:j<k)(hr:Diversity ( Z 0 ) j) : Z 0=0:= by
        induction j with
        | zero=>
           have hx: First Z a h 0 0:=⟨ fun _ h=>by omega, cometClean H _,hr ⟩; funext u t l; exact trim hr ( ( hx.flat ( t:=t ) (Response.mark H) ).trans ( lighter H hT hm 0 he hx ) ) l (by omega) -- trim in namespace
        | succ j ih=> have hx: First Z a h 0 (j+1):= ⟨ fun _ h=>by omega, cometClean H _,hr⟩; apply ih (by omega); intro p t l hl; exact trim hr (( hx.flat ( t:=t ) ( Response.mark H ) ).trans ( lighter H hT hm (j+1) he hx )) l (by omega)
    cases k with
    | zero=> funext p t l; exact limiter H hT hm h0 (a:=a) (t:=t) l (by omega)
    | succ k=> exact Hk k (by omega) (fun i t=>( limiter H hT hm h0 (a:=a) ).up (by omega))
open Literal
omit H hT hm h0 in
lemma empty_tune {W:Literal.Box ( Arts.Mob G )}(he: Mach.Ele h k 0 W)(hv:comet h 0 M.bulk ( gloss ( Literal.linear ( Arts.Mob G ) W )) X Q)(t:ℝ): letIn h (logMass t) X 0=0:= clean_zero hv (he.grows 0) he.Top he.2 t -- implicit variants
end YM.FVA2.Extras
