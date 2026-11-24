import YM.FormalBulk08.Spruce.Comb
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{Z:Frame G d}
variable {J U:X→ℕ}{F:∀ x:X,Flight (J x) (U x)}{V:∀ x:X,Lodge (F x).patch}{H:∀ x,(F x).patch.Branches K G}{L N:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {a:hue G}{ρ:ChartRatio G}{o: Loc G 1}
lemma multiplied (A B:X→ Studio D→ Tile (edgeL G) r){p q:X→ℝ}(hp:Faint τ g p)(hq:Faint τ (fun i=>δ i*g i) (p-q))(h:Brass τ o η δ (fun _=>1) A B): Tender τ o η (fun i=>δ i*g i) (fun i v=>p i • A i v-q i • B i v):=by
    have ht := Bear.pay (T:=fun i v=>A i v-B i v) (brass_cr _ _ h) hp; have he:=fade (Matched.right h) hq; unfold Tender at *; have hf: Tender τ o η (fun i=>δ i*g i) (fun i p'=> p i • (A i p'-B i p')):= by unfold Tender;convert ht using 1; ext i q;ring
    convert Bear.plus hf he using 1; ext1 i; ext1 v; rw [Pi.sub_apply,sub_smul,smul_sub]; abel
    -- type not defeq B costs. rewrite
lemma matchScale {A B: X→Anthem D G} {Y P: X→Roof.Plaza Z D } (e r:ℕ)(h:∀ i,Court o Z (Y i))(hp:∀ i,Court o Z (P i))(hv:∀ y n,n≤ e→Brass τ o η δ (fun _=>1) (fun i p=> Y i y p n r) (fun i p=> P i y p n r)) (he:∀ j k, j<e ∨ j=e∧ r≤ slots Z k → Faint τ g (fun i=>coeff j (echo Z (A i) k)) ∧ Faint τ (fun i=>δ i*g i) (fun i=> coeff j (echo Z (A i) k)-coeff j (echo Z (B i) k))): Tender τ o η (fun i=>δ i*g i) (fun i p=> crease Z (Y i) (A i) p e r - crease Z (P i) (B i) p e r ) := by
    unfold Tender crease; simp only [Kemp.launch,surf, Finset.sum_apply, ←Finset.sum_sub_distrib]; apply bear_sums _; intro i _; apply bear_sums _; intro j hj; rw [Finset.mem_antidiagonal] at hj; by_cases ht:j.1 < e∨ j.1=e∧ r ≤ Pose.slots Z i
    · obtain ⟨hz,hy⟩:= he _ _ ht; exact multiplied _ _ hz hy (hv i _ (by omega))
    have hz k p: Y k i p j.2 r=0:= Classical.byContradiction fun hP=> ht (by have hx:=((h k).officers i).fare.1 p j.2 r hP; unfold Yield at *; omega)
    have hh k p:P k i p j.2 r=0:= Classical.byContradiction fun hP=> ht (by have hx:=((hp k).officers i).fare.1 p j.2 r hP; unfold Yield at *;omega)
    simp_rw [hz,hh,smul_zero, sub_self]; exact bear_void ..

lemma capsule {P Q:X→Roof.Plaza Z D}{T S:X→ Anthem D G}{W Y: X→Pot G} (w:Wells τ F V H ρ a σ η δ L N W Y E)(c:Payroll K Z o (graded F L) V E R D τ σ η μ)(hδ:∀ i,0≤g i)(h:∀ i,Court o Z (P i))(he:∀ i,Court o Z (Q i)) (hT:∀ i,Clef o (T i) l)(ht:∀ i,Clef o (S i) l)(hp:∀ i, echo Z (T i)=0)(hQ:∀ i, echo Z (S i)=0)(hZ:∀ i,Qual (T i) o E (σ i))(hy:∀ i,Qual (S i) o E (σ i))(hr:r≤R+E)(hE:e≤E)(hs:d≤R)(hg:l≤R)(hL:∀ i,2≤(F i).L.val)
    (hx:∀ j k:ℕ,precede e r j k → Brass τ o σ δ g (fun i p=> T i p j k) (fun i p=> S i p j k))(hv:Tender τ o σ g (fun i p=> S i p e r))(hP:∀ j k,k ≤ e → Brass τ o η δ (fun _=>1) (fun i p=> P i j p k r) (fun i p=>Q i j p k r)) :
    let M(x):= migrates a (graded F L x) (V x) K (W x) ρ (H x) (hL x) d l (T x)
    let N'(x):= migrates a (graded F N x) (V x) K (Y x) ρ (H x) (hL x) d l (S x)
    Nextpay o τ σ η μ (fun i=> δ i*g i) r (fun i p=> T i p e r-S i p e r) (fun i p=> canopy Z (P i) (M i) p e r-canopy Z (Q i) (N' i) p e r) ∧
       ∀ j k, j<e ∨ j=e∧ r≤slots Z k → Faint τ (fun i=>δ i*g i) (fun i=> coeff j (echo Z (M i) k) - coeff j (echo Z (N' i) k)):= by
    intro M N'; let X i:=T i-S i; let g' i:=δ i*g i
    have hG i:0≤g' i:=mul_nonneg (w.dpos i) (hδ i)
    have h' i: Clef o (X i) l:= (hT i).sub (ht i)
    have hh: Mill d r e (graded F L) V K hL o τ η g' X (fun i=>M i-N' i):= crisped w hδ hL d l e r hE hx hZ hy hv
    have hu j k h: Tender τ o σ g' (fun i p=> X i p j k):= brass_crisp (hx j k h)
    have H1 j:Faint τ g' (fun i=> coeff e (echo Z (X i) j)):= by
        simp_rw [show ∀ i,echo Z (X i) j=(0:Pence) from fun i=> by unfold X;rw [chalk_less Z j (ht i).fare (hT i).fare,hp, hQ,sub_self],map_zero];apply faint_zero
    have hJ:= Fidelity c hh hu hE hr h' hg (fun i=> qual_sub (hZ i) (hy i)) H1 hG (by omega)
    have hX j k (he:j<e ∨ j=e∧ r≤ Pose.slots Z k): Faint τ g' (fun i=>coeff j (echo Z (M i) k)-coeff j (echo Z (N' i) k)):= by
        apply (hJ j k he).lower; intro x; have ha:Clef o (M x) l:= migrate_w (P:=graded F L x) a _ _ d (hT x) (w.aV x) (w.church x) w.pharmacy le_rfl; have hv: Clef o (N' x) l:= migrate_w (P:=graded F N x) a _ _ d (ht x) (w.bV x) (w.church x) w.pharmacy le_rfl; rw [chalk_less Z k hv.fare ha.fare,map_sub]
    refine ⟨?_,hX⟩
    obtain ha := Castor.terminal (V:=P) w.left c hL l l hT hZ hp hg hr hE hs hδ (fun j k h=> (hx j k h).1) h (fun j k h=> (hP j k h).1)
    have hw': Tender τ o η g' (fun i p=> crease Z (P i) (M i) p e r -crease Z (Q i) (N' i) p e r):= matchScale e r h he hP (fun j k h=> ⟨ha.2 k j h,hX j k h⟩)
    convert adhesion (ticker c hh hu hE hr h' hg H1 hG) hw' using 1; rotate_left
    · ext1 i; ext1 p; unfold canopy; simp only [Pi.sub_apply]; abel
    rfl
end YM.FormalBulk08.Spruce
