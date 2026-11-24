import YM.FormalBulk08.Sierra.Vow
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X:Type}{ρ:ChartRatio G}{T S:X→ Pot G}{τ:Time X}{E l u R:ℕ}{W: Lab G K X}
variable (h:Weather W u R E) (hp:Lab.Use W ρ E)(hs:G.Simple)(hv:LocalRatio ρ)(a:hue G)(C P Q:Pin W.scrolls)(o: Trail W C a)
variable {g:X→ℝ}
variable (hm:∀ i,C.N i ≤ P.N i)(hz:∀ i,P.N i≤ Q.N i)(hR:Erudit τ _ C)(hg:∀ i,0≤g i)(ht:∀ i,Ritual (T i) l)(hy:∀ i,Ritual (S i) l)(hl:l≤R)
lemma degZero (i: Deck C) : Degree 0 i=1:= by unfold Degree ratioR; simp
variable (hw:∀ e≤E,∀ r, Wit ((sage C).reach (peak C)) u (fun i=>o.rate (peak C i)) (fun i=>o.root (peak C i)) (hill C P hm) g (fun i=> T i e r) (fun i=> S i e r))
include h hp hs hv hm hg hz hR ht hy hl hw
lemma stoke : ∀ e≤E, Calm (rday τ C) (fun i=> hill C P hm i.a) (fun i=>g i.a) (fun i=>spice (satCamp ρ l a T C P i e 0)) (fun i=> spice (satCamp ρ l a S C Q i e 0)):= by
    let D:=hill C P hm
    obtain H0:= shorn h hp hs hv a C P Q o hm hz hg ht hy hl (θ:=0) (by norm_num) (fun i hi k hk=>hw i hi k); let A i:= satCamp ρ l a T C P i;let B i:=satCamp ρ l a S C Q i; have hh:=tabular hR.origin hR.depth hp.liable; let t:=qday τ C
    obtain w:=budge C P Q hm hz hp hv a hs; let L(x:Turn C):=graded W.liftF (W.trail P.N) x;let M(x:Turn C):=graded W.liftF (W.trail Q.N) x; let X'(x:Turn C):=Lab.instory ρ a W P.N x.ups;let Y (x:Turn C):=Lab.instory ρ a W Q.N (Turn.ups x);
    let f(x:Turn C)(j:ℕ):= plusB (L x) (W.liftU x) (X' x) (A x.ups) ρ (W.liftH x) l j 0; let g'(x:Turn C)(j:ℕ):=plusB (M x) (W.liftU x) (Y x) (B x.ups) ρ (W.liftH x) l j 0
    have hF j (hx:j≤E): Calm t (fun i=>D i.a) (fun i=>g i.a) (fun i=> spice (f i j)) (fun i=>spice (g' i j)):= by
       have HP x k (hk:x≤E)(hr:0<k): Wit (sage C) u o.rate o.root (fun i=> D i.a) (fun i=>g i.a) (fun i=> A i x k) (fun i=>B i x k) := by
           simpa only [Degree,ratioR, Real.rpow_zero,mul_one] using H0 x hk k hr
       have he: Wit (Dove.tide C) u (fun i=>o.rate i.bed) (fun i=>chief (L i) (o.root i.ups) (Exterior.coord 0,a)) (fun i=>D i.a) (fun i=>g i.a) (fun i=>f i j) (fun i=>g' i j):= plasters (o:=fun (i:Turn C) (_:Unit)=>o.root i.ups) (u:=u) (b:=fun i (_:Unit)=>g i.a) (T:=fun i _=>A i.ups) (S:=fun i _=>B i.ups) w (h.sails.reach (fun i:Turn C=> i.toLeaf)) (fun i=>o.cap i.bed) o.anchor j 0 l _ hx (fun j k he hk=> waxy Turn.ups (up_age C hp.liable) (g:=fun (i:Deck C)=>g i.a) (HP j k (by unfold precede at *;omega) hk))
       exact Calm.lifted id _ (hh.reach (fun i:Turn C=>i.bed)) (glow_v.mp he)
    have ht'(i:Turn C) : Fresh (epoch a (L i) (W.liftU i) K (X' i) ρ (W.liftH i)):= (sig_mat a _ (ripeness (F:=W.liftF) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
    have hv'(i:Turn C): Fresh (epoch a (M i) (W.liftU i) K (Y i) ρ (W.liftH i)):= (sig_mat a _ (ripeness (F:=W.liftF) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1
    obtain ⟨HA,HB⟩:=w.weight.goods ht' hv'
    intro e he
    induction e using Nat.strong_induction_on with
    | _ e ih=>
      let b i k:= Wine.bill (bookH (epoch a (L i) (W.liftU i) K (X' i) ρ (W.liftH i))) (bookU (epoch a (L i) (W.liftU i) K (X' i) ρ (W.liftH i))) e k 0
      let c i k:= Wine.bill (bookH (epoch a (M i) (W.liftU i) K (Y i) ρ (W.liftH i))) (bookU (epoch a (M i) (W.liftU i) K (Y i) ρ (W.liftH i))) e k 0
      let B'(i:Turn C):=braise (L i) (W.liftU i) (X' i) (A i.ups) ρ (W.liftH i) l;let C'(i:Turn C):=braise (M i) (W.liftU i) (Y i) (B i.ups) ρ (W.liftH i) l
      let Z (i:Turn C)(k):=b i k *spice (B' i k 0); let Z'(i:Turn C)(k):= c i k*spice (C' i k 0)
      have hh' k (hk:k<e): Calm t (fun i=> D i.a) (fun i=>g i.a) (fun i=>Z i k) (fun i=>Z' i k) := by
          have hP:= Calm.lifted Turn.ups t (soft_day t) (ih k hk (hk.le.trans he))
          have H : Calm t (fun i=>D i.a) (fun i=>g i.a) (fun i=>spice (B' i k 0)) (fun i=>spice (C' i k 0)):= by
             simp only [B',C', braiser,det0]; exact hP.sum (hF k (hk.le.trans he))
          exact H.growth (Pact_lift (g:=id) (hh.reach (fun i:Turn C=>i.bed)) (HA.income HB e k 0 (show e-k ≤ E by omega)) (fun i=>le_refl _))
      refine steepCalm hg (fun i=>limb_pos ..) ((hF e he).sum (calm_sums (Finset.range e) (fun i hi=>hh' i (Finset.mem_range.mp hi)))) ?_ (raySteps hR.depth) ?_ ?_
      · simp_rw [at_top]; exact Calm.lifted (τ:=(sage C).reach (peak C)) id τ (hh.reach (peak C)) (glow_v.mp (hw e he 0))
      · intro i; rw [score,enterStock,det0]; change (spice (A i.ups e 0) + (spice (f i e) + ((∑ k∈Finset.range e, b i k • B' i k 0): Tile (edgeL G) 0) default))- _= _; rw [add_sub_cancel_left,Finset.sum_apply];rfl
      intro i; rw [score,enterStock,det0]; change (spice (B i.ups e 0)+(spice (g' i e)+ ((∑ k∈Finset.range e,c i k • C' i k 0): Tile (edgeL G) 0) default))- _= _; rw [add_sub_cancel_left,Finset.sum_apply];rfl
-- thus supplies all moments in window-unit form if desired. nonconstant stronger via Soar direct.
end YM.FormalBulk08.Sierra
