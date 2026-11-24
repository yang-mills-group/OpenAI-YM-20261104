import YM.X.Scheme.Report
import YM.X.Jet.Reach
/-!
Prolongation of the whole correl hierarchy (on joint tests). `Arr` whenever through n with all inputs realizes exactly. Therefore coefficient at i uses only degrees ≤i.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Function Filter Set Pert Pert.Position Jet
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge}{F:Labels.Frames G} {d e n : ℕ}

-- directly all real test pairs before projecting via D
structure Appears {d : ℕ} (n:ℕ)(u:ℝ→Bank F d)(w:Word (Bank F d)) : Prop where
   writes : ∀ s:Section F d, Act n (lookie F s ∘ u) (lookie F s ∘ w)
local notation "M"=> Bank F d
local notation "Y"=> Buffer F d
variable {u:ℝ→Bank F d}{w:Word (Bank F d)}{b:Word (Buffer F d)}{v:ℝ→Buffer F d}
lemma Appears.discolor (h:Appears n u w) {k : ℕ}(t:Test k) : Act n (expose F t ∘ u) (expose F t ∘ w):=
   Act.all_picks fun i=> h.writes ⟨k,baring F d ∘ i,t⟩
lemma Appears.of_expose (h:∀ k (t:Test k), Act n (expose F t ∘ u) (expose F t ∘ w)): Appears n u w:= by
   refine ⟨fun s=>?_⟩
   let L : Lens F d s.r→ₗ[ℝ] ℂ:= ∑ i:Fin s.r→ChartIx F d, (∏ j,(baring F d).coord (i j) (s.p j)) • LinearMap.proj (R:=ℝ) (φ:=fun _=>ℂ) i
   have he(z:Bank F d): L (expose F s.f z)=lookie F s z:= by
      change _=z s.r s.f s.p; conv_rhs=>rw [← regain F z s.f,emerge,Bare.spread_value]
      haveI : IsZeroApply (Lens F d s.r→ₗ[ℝ] ℂ) (Lens F d s.r) ℂ:= by constructor; intro; rfl
      haveI : IsAddApply (Lens F d s.r→ₗ[ℝ] ℂ) (Lens F d s.r) ℂ:= by constructor; intros; rfl
      unfold L; rw [_root_.sum_apply];rfl
   convert! (h _ s.f).linear (L:=L.toContinuousLinearMap) using 1
   all_goals funext x; exact (he _).symm

lemma Appears.collect {X: Type*}[NormedAddCommGroup X][NormedSpace ℝ X] {g:Bank F d→ₗ[ℝ] X}(h:g∈ tableSpace F d X) (ha:Appears n u w):Act n (g ∘ u) (g ∘ w):= by
   induction h using Submodule.span_induction with
   | mem g hg=> obtain ⟨x,rfl⟩:=hg; exact (ha.writes x.1).linear (L:=(ContinuousLinearMap.id ℝ ℝ|>.smulRight x.2).comp (Complex.reCLM)) -- scalar?
   | zero=> simpa [Function.comp_def,show just (0:X)=(fun _=>0) from funext (fun i=> by unfold Jet.just; simp)] using (Act.static (n:=n) (0:X))
   | add f g hf hg h1 h2=> exact h1.add h2
   | smul r f hf h=> exact h.smul r
lemma Appears.pull (L:E F e →ₗ[ℂ] E F d)(h:Appears n u w): Appears n (pulls L ∘ u) (pulls L ∘ w):= ⟨fun s=> h.writes ⟨s.r,L ∘ s.p,s.f⟩⟩
lemma Appears.same {w':Word (Bank F d)}(h:Appears n u w)(he:Appears n u w'){i:ℕ}(hi:i≤n):w i=w' i:= by
   funext k t; ext1 p; let a : Pert.Position.Section F d:=⟨k,p,t⟩; exact (h.writes a).trans_at (he.writes a) hi
lemma appears_delay (w:Word (Bank F d))(n:ℕ): Appears n (delay w n) w:= by
   refine Appears.mk (fun k=>?_); let P:=lookie F k
   rw [show lookie F k ∘ delay w n=delay (lookie F k ∘ w) n from funext (fun i=> delay_map w P n i)]; exact Act.swell _ le_rfl
lemma Appears.turn (h:Appears n u w): Appears n (fun t=>u (-t)) (turn w):= by
   refine ⟨fun s=>?_⟩
   rw [show lookie F s ∘ Jet.turn w=Jet.turn (lookie F s ∘ w) from funext (fun i=> map_smul (lookie F s) _ _)]
   exact (h.writes s).reflects

/-- Upgrade under small moving frames b (no invertibility of b 0 needed here). -/
def predMarket {d:ℕ}(b: Word (Buffer F d)) (w: Word (Bank F d)) (i:ℕ):Bank F d:= fun k t=> emerge F (fun p=> Jet.run (cross F (baring F d ∘ p)) (Jet.pair (expose F t ∘ w) b) i)
lemma pred_leaves (s:Section F d)(ha: Appears n u w)(hb: Act n v b): Act n (fun t:ℝ=>lookie F s (market F (v t) (u t))) (Jet.run (cross F s.p) (Jet.pair (expose F s.f ∘ w) b)):= by
   simp_rw [cross_leaves]; exact ((ha.discolor s.f).zipper hb).transit (cross_smooth F s.p).contDiffAt
lemma appears_market (ha:Appears n u w)(hb:Act n v b): Appears n (fun t=> market F (v t) (u t)) (predMarket b w):= by
   refine Appears.of_expose (fun k t=> Act.all_picks (fun i=>?_)); let s: Section F d:= ⟨k,baring F d ∘ i,t⟩
   exact (pred_leaves s ha hb).repairs (fun j h=> Eq.symm (reads_emerge ..))
lemma pred_pulls {b:Word (Buffer F e)}{w: Word (Bank F e)}(h:d≤e): predMarket (zoomL F h ∘ b) (pulls (up F h) ∘ w) = pulls (up F h) ∘ predMarket b w:= by
   let L:=zoomL F h; let X:Buffer F e→L[ℝ] Buffer F d:= LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer F e) (F':=Buffer F d) L
   let U:=pulls (up F h); funext j; have hu:=appears_delay w j; have he:=Act.swell b (show j≤j from le_rfl)
   have hx : Act j (L ∘ delay b j) (L ∘ b):= by exact Act.linear (E:=Buffer F e) (G:=Buffer F d) (L:=X) he
   have hy:= hu.pull (up F h)
   have h1:= appears_market hy hx; have h2:= (appears_market hu he).pull (up F h)
   have ht : (fun t:ℝ=> market F (L (delay b j t)) (U (delay w j t))) = U ∘ (fun t=> market F (delay b j t) (delay w j t)):= funext fun i=> (market_proj _ _ _ h).symm
   exact Appears.same (show Appears j _ (predMarket (L ∘ b) (U ∘ w)) from (ht ▸ (show Appears j (fun t=>market F (L (delay b j t)) (U (delay w j t))) _ from h1))) h2 le_rfl
lemma pred_turn : predMarket (turn b) (turn w)=turn (predMarket b w):= by
   funext k
   have ht:= appears_delay w k; have he:= Act.swell b (show k≤k from le_rfl)
   exact (appears_market ht.turn he.reflects).same (appears_market ht he).turn le_rfl
lemma pred_par : predMarket (cPar F ∘ b) (pulls (par F d) ∘ w)= pulls (par F d) ∘ predMarket b w:= by
   funext k; let W:=delay w k; let B:=delay b k
   have hw:=appears_delay w k; have he:=Act.swell b (show k≤k from le_rfl)
   let U:=pulls (par F d); let X:Buffer F d→L[ℝ] Buffer F d:=LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=Buffer F d) (F':=Buffer F d) (cPar F)
   have ht := (appears_market hw he).pull (par F d)
   have hz := appears_market (hw.pull (par F d)) (he.linear (L:=X)); have h : (fun t:ℝ=> market F (X (B t)) (U (W t)))= U ∘ (fun t:ℝ=> market F (B t) (W t)) := funext fun i=> market_par ..
   exact Appears.same (show Appears k (U ∘ (fun t:ℝ=> market F (B t) (W t))) _ from (h ▸ (show Appears k (fun t:ℝ=> market F (X (B t)) (U (W t))) _ from hz))) ht le_rfl
lemma pred_zero : predMarket b w 0=market F (b 0) (w 0):= by funext k t; apply Module.Basis.ext_multilinear (fun _=>baring F d); intro i; let p:=baring F d ∘ i; change emerge F _ p=market F (b 0) (w 0) k t p; unfold p; rw [reads_emerge,run_zero]; exact cross_market .. 

end YM.PositionX
