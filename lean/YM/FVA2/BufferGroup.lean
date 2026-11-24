import YM.FVA2.EngineWeights
/-!
# Scale flow algebra: acts on all corner words. Zoom and strictly-lowering subgroup.
`Near.do` is based at identity, although other buffers admitted in acts (since ∆). Inverses
computed via REPORT on a *pure* array to get all finite quotient forms, uniqueness, and preserve
engineering slots. This is done to avoid building a group inverse formula unrelated to calibration.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace YM.FVA2.Verne
open Function Filter Set Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Detector PositionX.Ribbon Elegant PayAll ColorCode
open scoped Topology ContDiff Classical
variable {G:Gauge} (F: Labels.Frames G) {d e m:ℕ} {τ: Word ℝ}
local notation "B"=> Buffer F d
local notation "Ω"=> sameAxis F d
local notation "Φ"=> Word (Pert.Position.Buffer F d)
section grp
variable {F}
local notation "Ψ"=> E F d
local infixr:70 " ◃ "=> luxury
variable (a b c:Word (Buffer F d)) (v:Word (Bank F d)) (D: Detector F d)
lemma frameC_i : Injective (frameC F ( d:=d )) := by
    intro x y he; apply follows_right; exact add_left_cancel he
lemma composeH (a b c:Buffer F d) : settled (settled (a,b),c)=settled (a,settled (b,c)):= by apply frameC_i; simp only [frame_settled]; rfl
lemma assocH : (a ◃ b) ◃ c=a ◃ (b ◃ c):= by
    funext k; have he:= Act.swell a (show k≤k from le_rfl); have hv:= Act.swell b (show k≤k from le_rfl); have hx:=Act.swell c (show k≤k from le_rfl);
    let u(t:ℝ):= settled (delay a k t,settled (delay b k t,delay c k t)); let f:= fun t:ℝ=>settled (settled (delay a k t,delay b k t),delay c k t);
    have H:Act k f ((a ◃ b) ◃ c):= (((he.zipper hv).transit settled_diff.contDiffAt).zipper hx).transit settled_diff.contDiffAt; have h:f=u:= funext (fun _=>composeH ..);
    exact Act.trans_at (u:=u) (by rw [h] at H; exact H) ((he.zipper ((hv.zipper hx).transit (m:=settled) settled_diff.contDiffAt)).transit settled_diff.contDiffAt) le_rfl
lemma identity_t (p:Buffer F d): settled (p,0)=p∧ settled (0,p)=p:= by constructor <;> (apply frameC_i; simp only [frame_settled, frameC_zero]) <;> rfl
lemma justZ {R:Type*} [Zero R] : (just (0:R))=0:= funext fun i=>by unfold just; simp
lemma float (w: Word ( Bank F d )) : predMarket 0 w=w:= by
    funext k; let t:ℝ→ Buffer F d:= fun _=>0; have hz: Act k t 0:= justZ (R:=Buffer F d) ▸ (Act.static _); have hw:= appears_delay w k; have h: (fun i:ℝ=> market F (t i) ( delay w k i ))=delay w k:= funext fun _=> market_zero ..;
    exact Appears.same (by exact h ▸ (appears_market hw hz)) hw le_rfl -- metav
lemma town0 (w:PayAll.reprK F d m) : heated w 0=w:= by rw [heated,float]; exact mineIt _
lemma lIdent : 0 ◃ a=a := by
    funext k; have ha:= Act.swell a (show k≤k from le_rfl); let u :ℝ→ Buffer F d:= fun _=>0; have hu:Act k u 0:= justZ (R:=Buffer F d) ▸ (Act.static _); have H:(fun i:ℝ=> settled (u i,delay a k i))=delay a k:= funext fun i=> (identity_t _).2; exact Act.trans_at (H ▸ (show Act k (fun i=> settled (u i,delay a k i)) (0 ◃ a) from ((hu.zipper ha ).transit settled_diff.contDiffAt ))) ha le_rfl
lemma rIdent : a ◃ 0=a:= by
    funext k; have ha:= Act.swell a (show k≤k from le_rfl); let u:ℝ→Buffer F d:=fun _=>0; have hu: Act k u 0:= justZ (R:=Buffer F d) ▸ (Act.static _); have H:(fun i:ℝ=> settled (delay a k i,u i))= delay a k:= funext fun i=> ( identity_t _ ).1; exact Act.trans_at (H ▸ ( show Act k (fun i=>settled (delay a k i,u i)) (a ◃ 0) from (( ha.zipper hu ).transit settled_diff.contDiffAt))) ha le_rfl
lemma justH (p q:Buffer F d): just p ◃ just q= just (settled (p,q)):= funext fun i=> (((Act.static ( n:=i ) p).zipper ( Act.static q )).transit (m:=settled) (settled_diff.contDiffAt)).trans_at ( Act.static ..) le_rfl
lemma renZ {V:Type*}[AddCommGroup V][Module ℝ V](v:Word ℝ): ren v (0:Word V)=0:= by funext i; unfold ren order; simp
lemma renpair {V W:Type*}[ AddCommGroup V][Module ℝ V][ AddCommGroup W][Module ℝ W](x:Word ℝ)(v:Word V)(w:Word W): pair (ren x v) (ren x w)= ren x ( pair v w ):= by
    let t:= LinearMap.fst ℝ V W; let u:= LinearMap.snd ℝ V W; let k:=pair v w; funext i; exact Prod.ext (congr_fun (ren_writes t x k) i).symm (congr_fun (ren_writes u x k) i).symm
lemma renH {u:Word ℝ}(h:light u) : ren u (a ◃ b)= (ren u a) ◃ (ren u b):= by unfold luxury; rw [show Jet.pair (ren u a) (ren u b)=_ from renpair u a b, run_ren _ _ h settled_diff.contDiffAt ]
-- near kernel identity detect ∗.
def Stable (p:Word (Buffer F d)) := p 0=0
lemma stack (h:Stable a)(H:Stable b): Stable (a ◃ b):= by unfold Stable; rw [voters, show a 0=0 from h, show b 0=0 from H ]; exact ( identity_t _ ).1
lemma fast (h:Stable a)(hx:light τ) : Stable (ren τ a):= by unfold Stable; rw [ ren_light (V:=Buffer F d) hx a ]; exact h
lemma Hkindle (h:v 0=pureBank F d)(he:Stable a)(hv:predMarket a v=v)(hd:D.announce v 0): a=0:= by
    have hp:= solves_only D v h; rw [ hp.2.2 a he ( show D.announce v a from (by unfold announce at hd ⊢; rw [hv]; rw [float] at hd; exact hd) ), ← hp.2.2 0 rfl hd ] -- rw recursive? 
def undo : Φ:= let v:= just (pureBank F d); D.report (predMarket a v)
lemma report_st (h:v 0=pureBank F d): Stable (D.report v):= (solves_only D v h).2.1
lemma dawn (H:Stable a)(h:v 0=pureBank F d) : predMarket a v 0=pureBank F d:= by rw [ pred_zero, show a 0=0 from H,market_zero,h ]
lemma won (h:Stable a): Stable (undo a D)∧ a ◃ (undo a D)=0:= by
    let v:= Jet.just (pureBank F d); let q:=predMarket a v; let H: v 0= _ := if_pos (rfl: (0:ℕ)=0); -- inference
    have hm : q 0= pureBank F d:= dawn a v h H; obtain ⟨hV, he, hf⟩:= solves_only D q hm; refine ⟨he,?_⟩; obtain hc:= solves_only D v H;
    refine ( hc.2.2 (a ◃ undo a D) ( stack a _ h he ) ?_ ).trans (Eq.symm (hc.2.2 0 rfl ?_)); · unfold announce; rw [ ← together ]; exact hV
    unfold announce; rw [float]; unfold v; funext i; simp only [comp_apply]; unfold just; split <;> first| rfl| exact map_zero D.D
lemma reverse (h:Stable a): undo a D ◃ a=0:= by
    obtain ⟨he,hq⟩:= won a D h; let b:=undo a D; let c:=undo b D; have hu : b ◃ c=0:= (won b D he).2; change a ◃ b=0 at hq; have ht:c=a:= by rw [←lIdent c, ← hq, assocH, hu, rIdent ]; -- rw right inside?
    exact (Eq.symm (congr_arg (fun p=>luxury b p) ht)).trans hu
lemma unique (H:Stable a)(T:a ◃ b=0): b=undo a D:= by rw [← lIdent b, ← reverse a D H, assocH,T, rIdent]
lemma headline0 (h:v 0=pureBank F d): predMarket ( D.report v ) v 0 = pureBank F d:= dawn ( D.report v ) v (report_st _ _ h) h -- order
include D
lemma conditional (h:v 0=pureBank F d)(he:Stable a)(T: predMarket a v=v): a=0:= by
    let Rr:Φ:=D.report v; have hB:Stable Rr:= report_st _ _ h; have hm:= solves_only D v h;
    have hx:a ◃ Rr=Rr:= hm.2.2 _ (stack _ _ he hB) (by unfold announce; rw [ ← together, T ]; exact hm.1);
    have hf:a=(a ◃ Rr) ◃ undo Rr D:= by rw [ assocH, (won _ D hB).2, rIdent ]
    rw [hf,hx,(won _ D hB).2]
lemma riseD (h:v 0=pureBank F d)(ha:Stable a) : D.report v=a ◃ D.report (predMarket a v):= by
    obtain hV:= solves_only D v h; obtain hp:= dawn a v ha h; obtain hD:= solves_only D (predMarket a v) hp; symm; exact hV.2.2 _ ( stack _ _ ha hD.2.1 ) (by unfold announce; rw [← together ]; exact hD.1)
include D
lemma learn (h:v 0=pureBank F d)(ha:Stable a)(hb:Stable b)(T:predMarket a v=predMarket b v): a=b:= by
    have H: a ◃ undo b D=0:= conditional ( a ◃ undo b D ) v D h (stack _ _ ha (won _ D hb).1) (by rw [← together,T,together, (won b D hb).2,float ]);
    have h₀ : a= (a ◃ undo b D) ◃ b:= by rw [assocH, reverse _ D hb, rIdent ]
    rw [h₀,H,lIdent]
-- renormal cancellation An.η.Bank near uses asympt.Call.
end grp
end YM.FVA2.Verne
