import YM.FormalBulk08.Tundra.Crystal

/-! Close D cost at calibrated powers. Geometric payments in local coefficients. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Roof Quire Sable Aster Dawn Wine
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G: Gauge}{X:Type}{E m l r e u D:ℕ}{K:KernelChoices}{ρ:ChartRatio G}{a:hue G}
variable {J U:X→ℕ}{F:∀ i:X,Flight (J i) (U i)}{P:∀ i:X,Lodge (F i).patch}{V L:∀ i:X,Train (J i)}{H:∀ i,(F i).patch.Branches K G}{T S:X→Anthem D G}{W Y:X→ Pot G}
variable {τ:Time X}{σ η δ g:X→ℝ}{o:Loc G 1}{θ:X→ℝ≥0}
abbrev Wayfarer (T:X→Anthem D G)(e r:ℕ)(u:ℕ)(τ:Time X)(o:Loc G 1)(g:X→ℝ):Prop:= Whey u τ (fun _ _=> (0,o)) (fun _=>1) (fun i p=>g i*‖p‖) (fun i p=> T i p e r)
abbrev Blizzard (u:ℕ)(τ:Time X)(o: Loc G 1)(δ g : X→ℝ)(T S:X→Studio D→Tile (edgeL G) r):Prop:= Lacy u τ (fun _ _=>(0,o)) (fun _=>1) δ (fun i p=>g i*‖p‖) T S
abbrev Sigh (u:ℕ)(τ:Time X)(o: Loc G 1)(g:X→ℝ)(T:X→ Studio D→Tile (edgeL G) r):Prop:= Whey u τ (fun _ _=>(0,o)) (fun _=>1) (fun i p=>g i*‖p‖) T
variable (w:Wells τ F P H ρ a σ η δ V L W Y E)(h:Soft τ (fun i=> (η i)⁻¹))(hL:∀ i:X,2≤(F i).L.val)(hg:∀ i,0≤g i)
include w h hL hg
omit h w in
lemma steppingK (ht:Wayfarer T e r u τ o g)(M:∀ i:X,Train (J i)): Whey u τ (U:=fun i=>Studio D×Site (F i).L) (fun _ p=>(lift p.2,o)) (fun _=>1) (fun i p=>g i*‖p.1‖) (fun i p=>stepsong (graded F M i) (T i) (hL i) p.1 p.2 e r):= by
   obtain ⟨C,c,x,H⟩:=ht; refine ⟨C,c,x,fun i p=>?_⟩; exact (fled (lift p.2) o (H i (throughW p.2 _ (hL i) p.1))).mono (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (through_le ..) (hg i)) (x i))
omit h in
lemma landing (he: Blizzard u τ o δ g (fun i p=>T i p e r) (fun i p=> S i p e r)): Lacy u τ (U:=fun i=>Studio D×Site (F i).L) (fun _ p=>(lift p.2,o)) (fun _=>1) δ (fun i p=>g i *‖p.1‖) (fun i p=>stepsong (graded F V i) (T i) (hL i) p.1 p.2 e r) (fun i p=> stepsong (graded F L i) (S i) (hL i) p.1 p.2 e r):= by
    refine ⟨steppingK hL hg he.1 V,steppingK hL hg he.2 L,?_⟩; have hh : Wayfarer (fun i=> T i-S i) e r u τ o (fun i=>δ i*g i):= by unfold Wayfarer Whey; simp_rw [mul_assoc];exact he.3
    simp_rw [←mul_assoc]; exact steppingK hL (fun i=> mul_nonneg (w.dpos i) (hg i)) hh V
lemma grade_k (ht:Blizzard u τ o δ g (fun i p=> T i p e r) (fun i p=>S i p e r)) (d:ℕ): Blizzard u τ o δ g (fun i p=> Grail.blade (graded F V i) K (P i) (T i) d e r (hL i) p) (fun i p=> Grail.blade (graded F L i) K (P i) (S i) d e r (hL i) p):= by
   let Z(i:X):= Studio D×Site (F i).L; have hh:=colds (f:=fun i (p: Z i)=>chief (graded F V i) (lift p.2,o) o) (star_w w h (fun i=>show (1:ℝ≥0)≤1 from le_rfl) (fun i=>show (1:ℝ≥0) ≤ (F i).L.val*1 from by rw [mul_one];exact Nat.one_le_cast.mpr (F i).L.pos) o (landing w hL hg ht)); simp_rw [chief_h o _] at hh
   exact Matched.amp (m_sum_high (o:=fun _ _=>(0,o)) (b:=fun i (p:Studio D)=>g i*‖p‖) (soft_preim (fun i=>(F i).L) w.air) hh) (Pact.constant (soft_aven (fun i=>(F i).L) w.air d))
lemma strict_k (hx:e ≤ E)(ht:∀ i j,precede e r i j→0<j→ Blizzard u τ o δ g (fun x p=> T x p i j) (fun x p=> S x p i j))(d l:ℕ): Blizzard u τ o δ g (fun i p=> icons (graded F V i) ρ (P i) (W i) (H i) (T i) (hL i) d l e r p) (fun i p=> icons (graded F L i) ρ (P i) (Y i) (H i) (S i) (hL i) d l e r p):= by
   let Z(i:X):= Studio D × Site (F i).L
   have hh:= plasters (U:=Z) (T:=fun i z=>stepsong (graded F V i) (T i) (hL i) z.1 z.2) (S:=fun i z=>stepsong (graded F L i) (S i) (hL i) z.1 z.2) w h (fun i=>show (1:ℝ≥0)≤1 from le_rfl) (fun i=>show (1:ℝ≥0) ≤ (F i).L.val*1 from by rw [mul_one];exact Nat.one_le_cast.mpr (F i).L.pos) _ _ l o hx (fun j k hp hq=> landing w hL hg (ht j k hp hq));simp_rw [chief_h o _] at hh
   exact Matched.amp (m_sum_high (o:=fun _ _=>(0,o)) (b:=fun i (p:Studio D)=>g i*‖p‖) (soft_preim (fun i=>(F i).L) w.air) hh) (Pact.constant (soft_aven (fun i=>(F i).L) w.air d))
lemma blood (hx:e ≤ E)(ht:∀ i m,precede e r i m→ Blizzard u τ o δ g (fun x p=> T x p i m) (fun x p=> S x p i m))(d l:ℕ): Blizzard u τ o δ g (fun i p=> yetmore a (graded F V i) (P i) K (W i) ρ (H i) (T i) (hL i) d l e r p) (fun i p=>yetmore a (graded F L i) (P i) K (Y i) ρ (H i) (S i) (hL i) d l e r p):= by
    have hf i : Fresh (epoch a (graded F V i) (P i) K (W i) ρ (H i)):= (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
    have hv i : Fresh (epoch a (graded F L i) (P i) K (Y i) ρ (H i)):= (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1
    obtain ⟨HA,HB⟩:=w.weight.goods hf hv
    unfold Blizzard yetmore; apply Matched.plus (strict_k w h hL hg hx (fun i j hv _=>ht i j hv) d l);apply matched_sums _; intro j hj; rw [Finset.mem_range] at hj; apply Matched.amp _ (HA.income HB _ _ r (by omega)); simp_rw [quickse]; exact Matched.plus (grade_k w h hL hg (ht j r (Or.inl hj)) d) (strict_k w h hL hg (hj.le.trans hx) (fun i k h _=> ht i k (by unfold precede at *;omega)) d l)
lemma whole (hx:e≤ E)(ht:∀ i m,precede e r i m→ Blizzard u τ o δ g (fun x p=> T x p i m) (fun x p=> S x p i m))(hu: Blizzard u τ o δ g (fun i p=>T i p e r) (fun i p=> S i p e r))(d l:ℕ): Blizzard u τ o δ g (fun i p=> Roof.migrates a (graded F V i) (P i) K (W i) ρ (H i) (hL i) d l (T i) p e r) (fun i p=>Roof.migrates a (graded F L i) (P i) K (Y i) ρ (H i) (hL i) d l (S i) p e r):= by
    simp_rw [dawn_path]; exact Matched.plus (grade_k w h hL hg hu d) (blood w h hL hg hx ht d l)
end YM.FormalBulk08.Tundra
