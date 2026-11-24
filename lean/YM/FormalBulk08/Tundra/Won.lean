import YM.FormalBulk08.Tundra.Dollars

/-! Cutoff GDP for D and first step emissions. Captured stock may be subject to
just these polynomial bounds. Require model-phase as defined on same horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E m l e r u D R d:ℕ}{o:Loc G 1}{W:Lab G K X}{F:Frame G d}{T:SectionData F}{H:Hol G}{ρ:ChartRatio G}
variable {g δ:X→ℝ}{τ:Time X}{Y Z:X→Anthem D G}{θ:ℝ}

lemma serving {A B:X→Studio D→Tile (edgeL G) r}{p q:X→ℝ}(hp: Calm τ δ g p q)(h:Blizzard u τ o δ (fun _=>1) A B): Blizzard u τ o δ g (fun i v=>p i • A i v) (fun i v=>q i • B i v):= b_join (fading (Matched.left h) hp.aF) (fading (Matched.right h) hp.bF) (watermark A B hp.aF hp.diff h)
lemma servos {P Q:X→ Matrix (Letter F) Unit Pence} {Y Z:X→Roof.Plaza F D}(h:∀ i j,j≤ e→ Blizzard u τ o δ (fun _=>1) (fun x p=>Y x i p j r) (fun x p=> Z x i p j r))(hp:∀ i j,j≤e → Calm τ δ g (fun x=>coeff j (P x i ())) (fun x=>coeff j (Q x i ()))): Blizzard u τ o δ g (fun i p=>larch (Y i) (P i) () p e r) (fun i p=>larch (Z i) (Q i) () p e r):= by unfold Blizzard larch;simp only [Kemp.launch,surf,Finset.sum_apply]; apply matched_sums _;intro i _;apply matched_sums _;intro y hy; rw [Finset.mem_antidiagonal] at hy; exact serving (hp i y.1 (by omega)) (h i y.2 (by omega))
lemma mistup {A B S T:X→ Studio D→ Tile (edgeL G) r}(h:Blizzard u τ o δ g A B)(ht: Blizzard u τ o δ g S T): Blizzard u τ o δ g (fun i p=>A i p-S i p) (fun i p=>B i p-T i p):= by
    have hp:= Matched.amp ht (Pact.coin τ δ (-1));simp_rw [neg_one_smul] at hp;simp_rw [sub_eq_add_neg];exact Matched.plus h hp
open Dove.Lab Trellis Grail
variable (q:Quota F H W o D E R)(p:Nesting F D E R u W o)(v:Lab.Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)
   (C P Q:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hz:∀ i,P.N i≤Q.N i)(hl:l≤R)(hR:d≤R)
   (hg:∀ i,0≤g i)(hy:∀ i,Clef o (Y i) l)(hx:∀ i,Clef o (Z i) l)
   (hw:∀ e≤ E,∀ r,Blizzard u ((sage C).reach (peak C)) o (hill C P hp) g (fun x p=>Y x p e r) (fun x p=> Z x p e r))
   (Hq: Erudit τ _ C)(he:θ<1/2)(Ht:0≤θ)
include q p v h a hs ht hb hz hp hR Hq hx hy hw hl hg he Ht
lemma harvested (hn:e≤ E) (r:ℕ): Blizzard u (rday τ C) o (fun i=>hill C P hp i.a) (fun i=>g i.a*Degree θ i) (fun i t=>calmTop l T ρ Y q a C P i t e r) (fun i t=> calmTop l T ρ Z q a C Q i t e r) := by
    have H:=tabular Hq.origin Hq.depth v.liable; have H₁:= dayshore q p v h a hs ht hb C P Q hp hz hl hR hg hy hx hw he _ hn r
    refine mistup (ley (τ:=sage C) id H H₁) ?_; exact servos (P:=debt l T ρ q a C P Y) (Q:=debt l T ρ q a C Q Z) (Y:=tribal T q a (ρ:=ρ) P.N) (Z:=tribal T q a (ρ:=ρ) Q.N) (fun i j he=> ley (τ:=sage C) id H (bookings q p v h a hs ht hb C P Q hp hz hR _ (he.trans hn) r)) (fun i j hj=>bonvoyage q p v h a hs ht hb C P Q hp hz hl hR hg hy hx hw Hq he Ht i (hj.trans hn))
omit he Ht
lemma pinch (x: Letter F)(hn:e≤ E): Calm τ (hill C P hp) g (fun i=>coeff e (afloat l T ρ Y q a C P i x ())) (fun i=>coeff e (afloat l T ρ Z q a C Q i x ())):= by
    unfold afloat; simp only [Matrix.add_apply,map_add];apply Calm.sum
    · exact Calm.lifted (X:=X) (τ:=(sage C).reach (peak C)) id τ ((tabular Hq.origin Hq.depth v.liable).reach (peak C)) (muscle hw p.plus x e hn)
    have hv:=(bonvoyage q p v h a hs ht hb C P Q hp hz hl hR hg hy hx hw Hq (show (0:ℝ)<1/2 by norm_num) (le_refl 0) x hn).lifted (peak C) τ (soft_day _); exact hv.lapse (fun i=>by simp [Degree,ratioR]) (fun _=>limb_pos ..)
end YM.FormalBulk08.Tundra
