import YM.FVA2.DLead
/-!
# Exact cancellation in the detector in ambient jet calculus

At all sufficiently fine cutoffs. Also identify the limiting compatible formal normalization.
 No estimate of height ratios after multiplication by a future matrix.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Elegant
open Function Filter Set MeasureTheory PositionX
open Pert Pert.Position Maxwell Maxwell.Free PositionX.Bare.Shop PositionX.Jet
open PositionX.Ribbon PositionX.Detector
open Lattice Labels Topology
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F:Labels.Frames G} {d:ℕ}
    (D: Detector F d)(w:Word (Bank F d))(p u:Word (Buffer F d)){a:Word ℝ}
-- useful on exact finite data **whenever** needed.Construct seasonal patch.
local notation "Lo"=> pureBank F d
lemma lucid : D.patch (pureBank F d):= (D.slip_region).self_of_nhds
lemma solves_only (hv:w 0=pureBank F d) : D.announce w (D.report w)∧ D.report w 0=0∧ ∀ b, b 0=0→ D.announce w b→ b=D.report w:= by
    have he:= hv.symm ▸ lucid D; have hp : D.solve0 (w 0)=0:= (by rw [hv,solve0 ]; exact D.slip_spec.fixes); exact ⟨ D.patch_announces he,by rw [report_zero, hp ],fun b h=> D.patch_only he (h.trans hp.symm)⟩
section comp
lemma couple (ha: light a)(n:ℕ) : ren a (predMarket p w) n= predMarket (ren a p) (ren a w) n:= by
    let S(t):= delay w n t; let V:ℝ→ℝ:=delay a n;
    let K(t):= delay p n t; have hu := Act.swell a (show n≤n from le_rfl); have hx:=appears_delay w n; have hv:= Act.swell p (show n≤n from le_rfl);
    have hm {f:ℝ→ Bank F d}{W: Word (Bank F d)}(h:Appears n f W): Appears n (f ∘ V) (ren a W):= by refine ⟨fun s=>?_⟩; rw [ren_writes ]; exact hu.dial (h.writes s) ha -- F let masks
    exact (hm (appears_market hx hv )).same (appears_market (hm hx) ( hu.dial hv ha )) le_rfl
lemma warped (ha:light a)(hx:D.patch (w 0)): D.report ( ren a w )= ren a ( D.report w ):= by
    unfold report; rw [ren_writes ]; apply run_ren; exact ha; exact pick_nice hx
-- composition cancellation law. exact.Staged. Frame equality retained to tie new coefficient coordinates to pivot frame. needed to transfer pointwise too. PS.*
lemma strand {ι:Type*} {l:Filter ι} {u:ι→ Word ( Bank F d )}{w:ι→ Word ( Buffer F d )}{v:ι→Word ( Bank F d )}
    (h: ∀ᶠ i in l, predMarket (w i) (u i) = v i ) (h₀:Tendsto (fun i=> w i 0) l (𝓝 0))
    (hh: ∀ s: Section F d,Tendsto (fun i=> lookie F s (u i 0)) l (𝓝 (lookie F s Lo))) (hp:∀ s: Section F d,Tendsto (fun i=> lookie F s (v i 0)) l (𝓝 (lookie F s Lo))) :
    ∀ᶠ i in l, D.report ( u i )= Ribbon.luxury (w i) ( D.report (v i) ) ∧ predMarket (D.report ( u i )) (u i)= predMarket (D.report (v i)) (v i):= by
    let f(i n):= Ribbon.luxury (w i) (D.report (v i)) n;
    have hm : Tendsto (fun i=> f i 0) l (𝓝 0):= by
        let hp':= D.appears_solve0 (q:=fun i=>v i 0) hp; have he : settled ( ( 0,0 ):Buffer F d × Buffer F d)=0:= Subtype.ext (by simp [settled,follow_val]); unfold f; rw [ ← he ]; simp_rw [voters, report_zero ]; exact (settled_diff |>.continuous.continuousAt.tendsto).comp ( h₀.prodMk_nhds hp' )
    filter_upwards [ h, D.patches (q:=fun i=> u i 0) hh, D.patches (q:=fun i=>v i 0) hp, D.legal (q:=fun i=> u i 0) hh (v:=fun i=> f i 0) hm ] with i hi hm hc hk;
    have hx:D.announce (u i) (f i):= by unfold announce f; rw [← Ribbon.together,hi ]; exact D.patch_announces hc
    have hv:f i=D.report (u i):= by refine D.patch_only hm ?_ hx; apply Eq.symm (hk.mp ?_); obtain ht:= congr_fun (show D.D ∘ predMarket (f i) (u i)=_ from hx) 0; rw [Function.comp_apply,pred_zero ] at ht; exact ht; -- rw under ∑
    exact ⟨ hv.symm,Eq.trans (congr_arg (fun p=> predMarket p (u i)) hv.symm) (by unfold f; rw [ ← Ribbon.together, hi ])⟩
-- scalar compatibility: ren commute Bank Word (actor chord)
lemma same (ha:light a)(hv:D.patch (w 0)): predMarket (D.report (ren a w)) (ren a w) = ren a (predMarket ( D.report w ) w):= by rw [warped D w ha hv]; exact funext fun i=> (couple w _ ha i).symm
end comp
variable {I X Z:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Z][NormedSpace ℝ Z]{l:Filter I}
    {f:I→ Word ( Bank F d )}
def Wait (l:Filter I)(f:I→Word (Bank F d))(Z: Word (Bank F d)): Prop:=∀ i (s:Section F d), Tendsto (fun t=> lookie F s (f t i)) l (𝓝 (lookie F s (Z i)))
abbrev TurnsOn (l:Filter I)(f:I→Word X) (v:Word X): Prop:= ∀ i, Tendsto (fun t=> f t i) l (𝓝 (v i))
lemma present (v: Word X) {t:I→ Word X} (h:TurnsOn l t v) (g:X→Z)(hp: ContDiffAt ℝ ω g (v 0)): TurnsOn l (fun i=> run g (t i)) ( run g v ):= by intro i; let h:= jets_limit (fun j k=> t k j) v h i i g hp; exact h.const_smul _
lemma dropping {w: Word (Bank F d)} (h:Wait l f w) (i:ℕ)(p:Test i): TurnsOn l (fun i=> expose F p ∘ f i) (expose F p ∘ w):= fun j=> expose_leg (w:=fun i=> f i j) F ( h j ) p
lemma terms (h:Wait l f w)(hf:D.patch ( w 0 )) : TurnsOn l (fun i=>D.report ( f i )) ( D.report w ):= by
   apply present (D.read ∘ w) _ (pick D.slips) (pick_nice hf); exact fun i=> D.rail.common_limit (w:=fun j=> f j i) (h i)
lemma planner {w: Word (Bank F d)}{v:I→Word (Buffer F d)}{p:Word (Buffer F d)} (h:Wait l f w) (H:TurnsOn l v p) : Wait l (fun i=>predMarket (v i) (f i)) (predMarket p w):= by
   intro k t; simp_rw [ Ribbon.all_tips _ _ (s:=t) k]; apply present _ (t:=fun i=> Jet.pair _ _ ) _ _ (cross_smooth F t.p|>.contDiffAt) k; exact fun k=> (dropping h t.r t.f k ).prodMk_nhds ( H k )
end YM.FVA2.Elegant
