import YM.FormalBulk08.Tundra.Feel

/-! D cost without EXP on captured input, ɛ while ancestor reading.
Coupling-reset differences calibrated separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Castor Spruce
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I : Type}{E m n l e r d D R u:ℕ}{o:Loc G 1}{Z: Frame G d}
variable {τ:Time X}{σ η δ μ g:X→ℝ}
variable {T S:X→ Anthem D G}{P Q:X→ Roof.Plaza Z D}
lemma remains {T S:X→Studio D→Tile (edgeL G) r}(h:Blizzard u τ o δ g T S): Sigh u τ o (fun i=> δ i*g i) (fun i p=>T i p-S i p):=by unfold Sigh Whey; simp_rw [mul_assoc]; exact h.3
lemma aching {T S U:X→ Studio D→ Tile (edgeL G) r}(h:Sugar o τ u μ g r T S)(ht:Sigh u τ o g U) : Sugar o τ u μ g r T (fun i p=> S i p-U i p):= by
    obtain ⟨C,c,H,P⟩:=h; obtain ⟨A,a,b,V⟩:=ht; refine ⟨_,c.plus a,fun i=>add_nonneg (H i) (b i),fun i B hB F v=>?_⟩; apply (penn_sub (P i B hB F v) (V i v)).mono; apply le_of_eq; ring
lemma fading {T:X→Studio D→Tile (edgeL G) r}(ht:Sigh u τ o (fun _=>1) T){p:X→ℝ}(hv:Faint τ g p): Sigh u τ o g (fun i x=>p i • T i x):= by have ht:=Bear.pay (b:=fun i (q:Studio D)=>1 * ‖q‖) ht hv; simp only [one_mul] at ht; exact ht
lemma aching_at (e r)(h:∀ i,Court o Z (P i))(hv:∀ k t, t≤e→ Sigh u τ o (fun _=>1) (fun i p=> P i k p t r))(he:∀ j k,j<e ∨ j=e∧ r≤ slots Z k→Faint τ g (fun i=>coeff j (echo Z (T i) k))): Sigh u τ o g (fun i p=> crease Z (P i) (T i) p e r):= by
    unfold crease Sigh; simp only [Kemp.launch,surf,Finset.sum_apply]; apply bear_sums _; intro k _; apply bear_sums _; intro t ht; rw [Finset.mem_antidiagonal] at ht
    by_cases hh:t.1 < e∨ t.1=e∧ r≤ slots Z k
    · exact fading (T:=fun i p=> P i k p t.2 r) (hv k t.2 (by omega)) (he _ k hh)
    simp_rw [show ∀ i p,P i k p t.2 r=0 from fun i p=>by by_contra hk; have hp:=((h i).officers k).fare.1 p t.2 r hk; unfold Yield at *;omega, smul_zero]; exact bear_void ..
lemma watermark (A B:X→ Studio D→ Tile (edgeL G) r){p q:X→ℝ}(hp:Faint τ g p)(hq:Faint τ (fun i=>δ i*g i) (p-q))(h:Blizzard u τ o δ (fun _=>1) A B): Sigh u τ o (fun i=>δ i*g i) (fun i v=>p i • A i v-q i • B i v):=by
    have ht := Bear.pay (T:=fun i v=>A i v-B i v) (remains h) hp
    have hf: Sigh u τ o (fun i=>δ i*g i) (fun i p'=> p i • (A i p'-B i p')):= by unfold Sigh Whey; convert ht using 1;ext i q; ring
    unfold Sigh Whey; convert Bear.plus hf (fading (Matched.right h) hq) using 1; ext1 i; ext1 v; rw [Pi.sub_apply,sub_smul,smul_sub];abel
lemma match_c (e r:ℕ)(h:∀ i,Court o Z (P i))(hp:∀ i,Court o Z (Q i))(hv:∀ y n,n≤ e→Blizzard u τ o δ (fun _=>1) (fun i p=> P i y p n r) (fun i p=> Q i y p n r)) (he:∀ j k, j<e ∨ j=e∧ r≤ slots Z k → Faint τ g (fun i=>coeff j (echo Z (T i) k)) ∧ Faint τ (fun i=>δ i*g i) (fun i=>coeff j (echo Z (T i) k)-coeff j (echo Z (S i) k))): Sigh u τ o (fun i=>δ i*g i) (fun i p=>crease Z (P i) (T i) p e r - crease Z (Q i) (S i) p e r):= by
    unfold Sigh crease; simp only [Kemp.launch,surf,Finset.sum_apply, ← Finset.sum_sub_distrib]; apply bear_sums _;intro i _;apply bear_sums _; intro j hj;rw [Finset.mem_antidiagonal] at hj; by_cases ht:j.1<e∨j.1=e∧r≤Pose.slots Z i
    · obtain ⟨hz,hy⟩:= he _ _ ht; exact watermark _ _ hz hy (hv i _ (by omega))
    have hz k p:P k i p j.2 r=0:= Classical.byContradiction fun hP=>ht (by have hx:=((h k).officers i).fare.1 p j.2 r hP;unfold Yield at *;omega)
    have hh k p:Q k i p j.2 r=0:= Classical.byContradiction fun hP=>ht (by have hx:=((hp k).officers i).fare.1 p j.2 r hP;unfold Yield at *;omega)
    simp_rw [hz,hh,smul_zero,sub_self];exact bear_void ..

variable {J U:X→ℕ}{F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{L N:∀ i:X,Train (J i)}{W Y:X→Pot G}{ρ:ChartRatio G}{a:hue G}
lemma rail (w:Wells τ F V H ρ a σ η δ L L W W E)(q:Ticket K Z o (graded F L) V E R D u τ μ)(h:Soft τ (fun i=>(η i)⁻¹))(hg:∀ i,0≤g i)(hp:∀ i,Clef o (T i) l)(hx:∀ i, echo Z (T i)=0)(he:e≤E)(hr:r≤R+E)(hy:l ≤ R)(hL:∀ i,2≤(F i).L.val)(ht:∀ j k:ℕ,precede e r j k→Wayfarer T j k u τ o g)(hQ:∀ i,Court o Z (P i))(hb:∀ k j, j≤e→ Sigh u τ o (fun _=>1) (fun i p=> P i k p j r)) (t : ℕ):
   let M i:= migrates a (graded F L i) (V i) K (W i) ρ (H i) (hL i) d t (T i)
   Sugar o τ u μ g r (fun i p=> T i p e r) (fun i p=>canopy Z (P i) (M i) p e r) ∧∀ y j,j<e ∨ j=e∧r≤Pose.slots Z y→ Faint τ g (fun i=> coeff j (echo Z (M i) y)):= by
    intro M; have ht' k:Faint τ g (fun i=>coeff e (echo Z (T i) k)):= by simp_rw [hx, Pi.zero_apply,map_zero]; apply faint_zero
    have hR: Reachable d r e u (graded F L) V K hL o τ g T M:= by
        refine ⟨?_,fun j k hj=> Matched.left (whole w h hL hg (by unfold precede at *;omega) (fun i m hi=> Matched.constant (ht i m (by unfold precede at *;omega))) (Matched.constant (ht _ _ hj)) d t)
          ⟩
        · unfold Sigh M; simp_rw [dawn_path, add_sub_cancel_left]; exact Matched.left (blood w h hL hg he (fun i j hz=>Matched.constant (ht i j hz)) d t)
    have hW j k hj:= loss q hR ht he hr hp hy ht' hg j k hj
    exact ⟨aching (vapor q hR ht he hr hp hy ht' hg) (aching_at e r hQ hb hW),fun y j hv=>hW j y hv⟩
lemma slide (w:Wells τ F V H ρ a σ η δ L N W Y E)(q:Ticket K Z o (graded F L) V E R D u τ μ)(h:Soft τ (fun i=>(η i)⁻¹))(hg:∀ i,0≤g i)(hQ:∀ i,Court o Z (P i))(hW:∀ i,Court o Z (Q i)) (hT:∀ i,Clef o (T i) l)(ht:∀ i,Clef o (S i) l)(hp:∀ i,echo Z (T i)=0)(hs:∀ i,echo Z (S i)=0)(hr:r ≤ R+E)(he:e ≤ E)(hy:l ≤ R)(hL:∀ i,2≤(F i).L.val)
   (hx:∀ j k:ℕ,precede e r j k→ Blizzard u τ o δ g (fun i p=> T i p j k) (fun i p=> S i p j k))(hv:Wayfarer S e r u τ o g)(hP:∀ j k,k≤e → Blizzard u τ o δ (fun _=>1) (fun i p=> P i j p k r) (fun i p=> Q i j p k r)) :
    let M(x):= migrates a (graded F L x) (V x) K (W x) ρ (H x) (hL x) d l (T x)
    let O(x):= migrates a (graded F N x) (V x) K (Y x) ρ (H x) (hL x) d l (S x)
    Sugar o τ u μ (fun i=> δ i*g i) r (fun i p=>T i p e r-S i p e r) (fun i p=>canopy Z (P i) (M i) p e r-canopy Z (Q i) (O i) p e r) ∧
       ∀ j k,j<e ∨ j=e∧r≤slots Z k → Faint τ (fun i=>δ i*g i) (fun i=> coeff j (echo Z (M i) k) - coeff j (echo Z (O i) k)):= by
    intro M O;let D' i:=T i-S i;let g' i:=δ i*g i;have hd i:0≤g' i:=mul_nonneg (w.dpos i) (hg i)
    have h' i: Clef o (D' i) l:= (hT i).sub (ht i); have hJ: Faint τ g' (fun _=>0):= faint_zero ..
    have hh: Reachable d r e u (graded F L) V K hL o τ g' D' (fun i=> M i-O i):= by
       refine ⟨?_,fun j k hj=> remains (whole w h hL hg (by unfold precede at *;omega) (fun i m hi=> hx i m (by unfold precede at *;omega)) (hx j k hj) d l)⟩
       have hB:= remains (blood w h hL hg he hx d l); have hw:= remains (grade_k w h hL hg (T:=S) (S:=S) (Matched.constant hv) d)
       unfold Sigh Whey; convert Bear.plus hB hw using 1; ext1 i; ext1 p
       obtain ⟨A,C,ha,hc,V'⟩:= (hT i).fare.2.2 e r; obtain ⟨B,W,hb,b,Q⟩:=(ht i).fare.2.2 e r; obtain ⟨T0,h0,E,U⟩:= w.carts.left.zeal
       dsimp only [M,O,D']; simp only [Pi.sub_apply,dawn_path, blade_difference (graded F L i) (V i) K _ _ _ _ (o:=o) (η:=0) (σ:=0) (by simp) le_rfl (fun j=>penn_shrink (V' j) ha.le) (fun j=>penn_shrink (Q j) hb.le) (strip_mono (U i) (w.pay.output i).le le_rfl) (E i)];abel
    have hu (j k:ℕ)(he:precede e r j k): Wayfarer D' j k u τ o g':= remains (hx j k he)
    have H1 j:Faint τ g' (fun i=>coeff e (echo Z (D' i) j)):= by
       simp_rw [show ∀ i,echo Z (D' i) j=(0:Pence) from fun i=>by unfold D';rw [chalk_less Z j (ht i).fare (hT i).fare,hp,hs,sub_self],map_zero];exact hJ
    have hx' j k (hl:j<e∨ j=e∧ r≤slots Z k): Faint τ g' (fun i=>coeff j (echo Z (M i) k)-coeff j (echo Z (O i) k)):= by
        apply (loss q hh hu he hr h' hy H1 hd j k hl).lower; intro x; have ha: Clef o (M x) l:= migrate_w (P:=graded F L x) a _ _ d (hT x) (w.aV x) (w.church x) w.pharmacy le_rfl; have hv: Clef o (O x) l:=migrate_w (P:=graded F N x) a _ _ d (ht x) (w.bV x) (w.church x) w.pharmacy le_rfl; rw [chalk_less Z k hv.fare ha.fare,map_sub]
    refine ⟨?_,hx'⟩
    obtain ha:= rail w.left q h hg hT hp he hr hy hL (fun j k h=>(hx j k h).1) hQ (fun k j h=>(hP k j h).1) l; have hw': Sigh u τ o g' (fun i p=> crease Z (P i) (M i) p e r- crease Z (Q i) (O i) p e r):= match_c e r hQ hW hP (fun j k h=> ⟨ha.2 k j h,hx' j k h⟩)
    convert aching (vapor q hh hu he hr h' hy H1 hd) hw' using 1;rotate_left
    · ext1 i;ext1 p;unfold canopy;simp only [Pi.sub_apply];abel
    rfl
end YM.FormalBulk08.Tundra
