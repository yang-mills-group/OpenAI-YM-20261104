import YM.FVA2.RateC
/-!
# Alignment and scale in both schemes respects coupling sign with Wick parity
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.Plot
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet PositionX.Detector
open Panel ColorCode Pic Forge Forge.Parity BoxOffice Verne Strat Hop PositionX.Ribbon Month
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}{F:Labels.Frames G}{d:ℕ}
section
-- not circular. transfer orth parity operator on frames
local notation "Q"=> cPar F (d:=d)
lemma follow_parity (a b:Buffer F d): Q (followB a b)= followB (Q a) (Q b):= by
   apply follows_right; apply LinearMap.ext; intro p; rw [ follow_buff ]; change ( cPar F (followB a b) ).val p= (cPar F a).val ((cPar F b).val p); rw [ cPar_eq,cPar_eq,cPar_eq,par_cycle ]; rfl
lemma TurnC (a b:Word (Buffer F d)) : turn (luxury a b)=luxury (turn a) (turn b):= by
    funext n; have ha:= Act.swell a (n:=n) le_rfl; have hv:= Act.swell b (n:=n) le_rfl; let z(x:ℝ):=(delay a n x,delay b n x); let L:= luxury a b; have ht:Act n (settled ∘ z) L:= (ha.zipper hv).transit settled_diff.contDiffAt; exact ht.reflects.trans_at ((ha.reflects.zipper hv.reflects).transit (m:=settled) settled_diff.contDiffAt) le_rfl
abbrev sepSim (T: Word (Buffer F d)): Prop:= Q ∘ turn T=T
-- not δ-proof: apply elegant uniqueness
lemma art (p:Word (Buffer F d)) (X:Word (Bank F d)) (D: Detector F d)(he:D.announce X p)(h:X 0=pureBank F d)(hq:elliptic X)(hv:p 0=0): sepSim p := by
   let U:= pulls (par F d); let Z:= cPar F (d:=d); have hY : D.announce X (Z ∘ turn p):= by
       let T:=turn p; have hh:U ∘ X=turn X:=hq; have ht : U (pureBank F d)=pureBank F d:= by rw [← h]; exact (congr_fun hh 0).trans (turn_zero _);
       have hU: U ∘ turn X=X:= by rw [←hh ]; exact funext fun i=> pulls_p ..;
       unfold Detector.announce; rw [show predMarket (Z ∘ turn p) X= _ from ?_] -- annotate
       · show D.D ∘ (U ∘ turn (predMarket p X))= _; funext i; change D.D ( U ( (-1:ℝ)^i • predMarket p X i ))= _; rw [map_smul,map_smul,D.color,show D.D ( predMarket p X i )=_ from congr_fun he i ]; unfold just; split
         next hi=> subst i; rw [ pow_zero,one_smul, ← D.color, show pulls (par F d) _= _ from ht]
         next _=> rw [map_zero,smul_zero ]
       · conv_lhs => rw [ ← hU ]; -- realigns.D. span
         unfold Z U; rw [ pred_par, pred_turn ]; -- finish
   obtain hp:= Elegant.solves_only D X h; have hh: Stable ( Z ∘ turn p ):= by unfold Stable; rw [comp_apply,turn_zero,hv,map_zero ]
   exact (hp.2.2 _ hh hY).trans (hp.2.2 _ hv he).symm
-- stronger: transported sig.Deg.
variable (X Y: Strat F) {s v:Word ℝ}
abbrev slant := ∀ d, sepSim ( X.wire d )
lemma slant_p (hx:slant X)(hy:slant Y): slant (X*Y):= by intro d; unfold sepSim at *; rw [ Strat.pay, TurnC, Verne.transported _ _ _ follow_parity, hx d,hy d ]
lemma turnsR (he:turn s= -s)(hx:light s){E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](p:Word E): turn (ren s p)=ren s (turn p):= by rw [← ren_turn_x p hx, he, ren_turn_v _ hx ]
lemma slantN (h:slant X)(he:turn s= -s)(hs:light s): slant (resume X s):= by intro d; unfold sepSim; rw [resume_wire,turnsR he hs (X.wire d), Jet.ren_writes _ s,h d ]
set_option maxRecDepth 4000 in
private lemma Φ (i:ℕ)(p:Buffer F d): Q (Down F ( get i ) ( get i ) p)= Down F ( get i ) ( get i ) ( Q p ):= by
    ext1; ext1 v; rw [ cPar_eq ]; let R:= get i; let P:= Verne.eng F R d; have hT(v:E F d): par F d ( P v )= P (par F d v):= by unfold P par eng; rw [scalePol_mul,scalePol_mul,mul_comm ]; -- bad.Tactic
                                                                            -- ...
    change par F d ( P ( p.val ( P ( par F d v ) )))= P (( cPar F p ).val ( P v )); rw [hT, cPar_eq,hT ];
lemma slant_only (he:slant X): slant (Strat.only X):= by
    intro d; unfold sepSim; funext k; let F0(d'):=( X.wire d' ); let Lp:=withinBlock F (d:=d); have hp: cPar F ( (Parity.segment k) • (X.wire d k) )= X.wire d k:= congr_fun (he d) k; change cPar F ( ( Parity.segment k ) • ( Lp ( X.wire d k ) ) )= Lp ( X.wire d k ); rw [ ← map_smul ]; have he : ∀ i:Buffer F d,(cPar F (d:=d)) (Lp i)= Lp (cPar F i):= fun i=> by unfold Lp withinBlock; rw [ LinearMap.sum_apply, LinearMap.sum_apply, map_sum ]; simp_rw [Φ ]; -- trick
    rw [ he,hp ]
lemma slantΛ (x:ℝ): slant (Λ F x):= by
    intro d; unfold sepSim; funext k; rw [Λwire ]; simp only [ Function.comp_apply ]; unfold turn just; split; swap; · rw [smul_zero,map_zero ]
    next h=> subst k; rw [pow_zero,one_smul ]; ext1; ext1 p; rw [cPar_eq ]; change par F d ( Δ F x d (par F d p)-par F d p )=Δ F x d p - p; rw [ map_sub, ← sign_Δ, par_cycle ];
-- slant inverses, transfer X formal frame.L.
lemma slantI (h:slant X)(hx:pulse X)(T:(d:ℕ)→ Detector F d): slant (refresh T X hx):= by
    intro d; have hz:sepSim ( (1:Strat F).wire d ):= slantΛ 0 d; let U:= refresh T X hx; let L:= cPar F (d:=d); have hp:luxury (X.wire d) (U.wire d)=(1:Strat F).wire d:= congr_arg (fun t: Strat F=> t.wire d) (( right_refresh T X hx ).2.1);
    apply Verne.unique ( X.wire d ) (L ∘ turn (U.wire d) ) (T d) (hx d); nth_rw 1 [ ← h d ]; rw [← Verne.transported _ _ L follow_parity,← TurnC,hp]; exact hz.trans ( zeroed F d )
lemma signD (d:ℕ) (D:Detector F d)(X:Word (Bank F d))(ht:X 0=pureBank F d)(he:elliptic X): sepSim (D.report X):= art ( D.report X ) X D ( Elegant.solves_only D X ht |>.1 ) ht he ( Elegant.solves_only D X ht|>.2.1 )
def sloping (X:Hop F) : Prop:= turn X.f= -X.f ∧ slant X.Z
lemma lampM (X G:Hop F)(hf: sloping X)(hg:sloping G): sloping (X*G) := by
    unfold sloping; rw [ walkF,walkZ,turnsR hg.1 G.rooted X.f,hf.1 ]; exact ⟨ (ren_writes (-LinearMap.id) G.f X.f ).symm, slant_p _ _ ( slantN _ hf.2 hg.1 G.rooted ) hg.2 ⟩
lemma haltM {T:Hop F}(hf:sloping T)(x:ℝ): sloping (glance x T):= ⟨ hf.1, slant_p _ _ ( slant_p _ _ (slantΛ _ ) hf.2 ) ( slantΛ x ) ⟩
lemma driftM {T:Hop F} (D:(d:ℕ)→ Detector F d)(ht:sloping T): sloping (undoV T D):= by
    have he:= invert_odd T.loved ht.1; exact ⟨ he, slantN _ ( slantI _ ht.2 T.tangent D ) he ( Jet.lives _ ) ⟩
end
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
include h
lemma turnL (s:ℝ): slant (Pic.L V M s h):= by
    have he(d):= sign_v V M (s:=s) d; simp_rw [ Pic.payMark ] at he; intro d; let T:=nested V.F h (warehouse V); exact signD d (T d) (Spring.ms V M s d) (Spring.vintage_ms .. ) (he d)
lemma metricL (s:ℝ)(P:Pic.pass V h M R): sloping (Forge.Pay V M R P s) := by
    obtain hv:= inverse_odd V M R s P; exact ⟨ hv,slantN _ ( turnL V M s ) hv ( transfer V M R s P ).rooted ⟩
lemma turnZ (s:ℝ)(P: Pic.pass V h M R): sloping (Forge.transfer V M R s P) := ⟨ inverse_odd V M R s P, slant_only _ ( metricL V M R s P |>.2 ) ⟩
variable (s)(v:ℝ)(P:Pic.pass V h M R)
lemma ChooseB : slant ( chooseN V M R s P ):= slant_p _ _ ( slantI _ (metricL V M R s P|>.2) _ _ ) ( turnZ V M R s P |>.2 )
lemma raysM : sloping ( diffuse V M R v s P ):= lampM _ _ ( metricL V M R s P) ( driftM _ ( metricL V M R (s-v) P) )
lemma ltX : sloping ( xflow V M R v s P ) ∧ sloping ( cflow V M R v s P ):= by obtain he:= raysM V M R (s:=s) v P; have ht{C:Hop V.F}(h₁:sloping C): sloping ( slideOf V (h:=h) v C (diffuse V M R v s P)):= lampM _ _ ( lampM _ _ ( driftM _ h₁ ) he ) ( haltM h₁ _ ); exact ⟨ ht (metricL V M R s P),ht (turnZ V M R s P) ⟩
lemma βM_odd (t:ℕ)(hT: Even t): Month.β ( Forge.Mray V h M R s P ) t=0:= by
    have hx(v:ℝ): ψ (Forge.Mray V h M R s P) v t=0:= Plot.parity0 ( Plot.raysM V M R (s:=s) v P |>.1 ) t hT; unfold Month.β; rw [funext hx]; simp
end YM.FVA2.Plot
