import YM.FormalBulk08.Sierra.Coal
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{E n m u e l r:ℕ}{X I:Type}
variable {τ:Time X}{μ η σ δ g:X→ℝ}{ε θ:X→ℝ≥0}{o κ:X→edgeL G}{T S:X→ Pot G}
def Gleam (τ:Time X)(r u:ℕ)(μ g:X→ℝ)(o x:X→edgeL G)(ε θ:X→ℝ≥0)(T S:X→Tile (edgeL G) r):Prop:=∃ B:X→ℝ,Soft τ B∧(∀ i,0≤B i) ∧∀ i A, Knoxville (grain (fame _) (ε i)) u (o i) (T i) A→ Knoxville (grain (fame _) (θ i)) u (x i) (S i) (μ i*A+B i*g i)
lemma warm {T U W:X→Tile (edgeL G) r}(h: Gleam τ r u μ g o κ θ ε T U)(hp:Wake τ u ε κ g W): Gleam τ r u μ g o κ θ ε T (fun i=>U i+W i):= by obtain ⟨C,c,H,X⟩:=h; obtain ⟨D,d,Q,P⟩:=hp; refine ⟨_, c.plus d,fun i=>add_nonneg (H i) (Q i),fun i A he=>?_⟩;rw [add_mul,←add_assoc];exact (X i _ he).add (P i ())
lemma rivals {Y T:X→ Tile (edgeL G) r}(h:Wit τ u ε o δ g T Y): Wake τ u ε o (fun i=>δ i*g i) (T-Y):= h.3
lemma nominees (h:∀ j k,j<e→0<k → k≤r → Wake τ u θ o g (fun i=> T i j k))(he:∀ i,0≤ g i): ∃ B:X→ℝ,Soft τ B ∧ (∀ i,0≤B i) ∧ ∀ i, Peaks e r (T i) (o i) u (θ i) (B i*g i):= by
    let s:Finset (ℕ×ℕ):= (Finset.range e) ×ˢ Finset.Icc 1 r; choose! C c v H using fun p:↥s=> h p.val.1 p.val.2 (Finset.mem_range.mp (Finset.mem_product.mp p.property).1) ((Finset.mem_Icc.mp (Finset.mem_product.mp p.property).2).1) ((Finset.mem_Icc.mp (Finset.mem_product.mp p.property).2).2)
    let B i:=∑ j,C j i; have hp i:0≤ B i:=Finset.sum_nonneg (fun j _=> v j i)
    refine ⟨B,soft_bill _ (fun i _=> c i),hp,fun i=>⟨mul_nonneg (hp i) (he i),fun j hj k hk hu=>?_⟩⟩
    let a:↥s:=⟨(j,k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,Finset.mem_Icc.mpr ⟨hk,hu⟩⟩⟩;exact (H a i ()).mono (mul_le_mul_of_nonneg_right (show C a i≤B i from Finset.single_le_sum (fun j _=> v j i) (Finset.mem_univ a)) (he i))
variable {j t:X→ℕ}{F:∀ i:X,Flight (j i) (t i)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{L N:∀ i:X,Train (j i)}{ρ:ChartRatio G}{a:hue G}{W Y:X→Pot G}
    (h:Soft τ (fun i=>(η i)⁻¹))(he:∀ i,ε i≤1)(hv:∀ i, θ i≤1)(hf:∀ i,ε i ≤(F i).L.val*θ i)(hr:0<r)(hx:e≤ E)(hg:∀ i,0≤g i)
def Paper (K:KernelChoices)(F:∀ i:X,Flight (j i) (t i))(V:∀ i:X,Lodge (F i).patch)(u l e r:ℕ)(τ:Time X)(G:Gauge)(μ:X→ℝ):Prop:=∃ C:X→ℝ,Soft τ C ∧(∀ i,0≤C i)∧∀ i,Perusal K (F i) (V i) u l e r G (μ i) (C i)
include h he hv hf hr hx hg
omit h hr hx in
lemma fire_one (a:Loc G 1)(w:Paper K F V u l e r τ G μ)(ht:∀ i,Ritual (T i) l)(hz:∀ j k,j<e→ 0<k→ k≤r → Wake τ u θ o g (fun i=> T i j k)): Gleam τ r u μ g o (fun i=>chief (F i) (o i) a) θ ε (fun i=>T i e r) (fun i=>Det (F i) (V i) K (T i e r)):= by
    obtain ⟨C,c,w',P⟩:=w; obtain ⟨B,b,V',H⟩:=nominees hz hg; refine ⟨_,c.times b,fun i=>mul_nonneg (w' _) (V' _),fun i A H'=>?_⟩;rw [mul_assoc];exact (P i).mark (T i) (ht i) a (o i) _ _ (he i) (hv i) (hf i) _ _ H' (H i)
lemma noel (w:Wells τ F V H ρ a σ η δ L L W W E)(c:Paper K (graded F L) V u l e r τ G μ)(hT:∀ i,Ritual (T i) l)(hp:∀ j k,precede e r j k→0<k → Wake τ u θ o g (fun i=> T i j k)) :
    Gleam τ r u μ g o (fun i=> chief (F i) (o i) (Exterior.coord 0,a)) θ ε (fun i=> T i e r) (fun i=>enterStep (graded F L i) (V i) (W i) a ρ (H i) l (T i) e r):= by
    have ho:=Matched.left (strict_pair (l:=l) w h he hf hr hx (fun j k hj hk=>Matched.constant (hp j k hj hk)))
    have hv' := fire_one (F:=graded F L) he hv hf hg (Exterior.coord 0,a) c hT (fun j k hj hk _=>hp j k (Or.inl hj) hk)
    convert warm hv' ho using 1 <;> try rfl
    funext i;abel -- sum A+(B-A); needs add_sub_cancel ..
lemma tote (w:Wells τ F V H ρ a σ η δ L N W Y E)(c:Paper K (graded F L) V u l e r τ G μ)(hT:∀ i,Ritual (T i) l)(hS:∀ i,Ritual (S i) l)(hp:∀ j k, precede e r j k→0<k → Wit τ u θ o δ g (fun i=>T i j k) (fun i=> S i j k))(hb: Wake τ u θ o g (fun i=> S i e r)): Gleam τ r u μ (fun i=>δ i*g i) o (fun i=> chief (F i) (o i) (Exterior.coord 0,a)) θ ε (fun i=>T i e r-S i e r) (fun i=>enterStep (graded F L i) (V i) (W i) a ρ (H i) l (T i) e r-enterStep (graded F N i) (V i) (Y i) a ρ (H i) l (S i) e r):= by
    have he':= rivals (strict_pair (l:=l) w h he hf hr hx hp); let Z i:= T i-S i; let κ(i:X):= chief (F i) (o i) (Exterior.coord 0,a); let t i:=δ i*g i
    let x(i:X):= S i e r; let v(i):= Det (graded F L i) (V i) K (x i);let z(i):= Det (graded F N i) (V i) K (x i); have hZ:Wake τ u ε κ t (v-z) := rivals (T:=v) (Y:=z) (colds (star_w w h he hf (Exterior.coord 0,a) (Matched.constant hb)))
    obtain heH:= fire_one (F:=graded F L) he hv hf (fun i=>mul_nonneg (w.dpos i) (hg i)) (T:=Z) (o:=o) (Exterior.coord 0,a) c (fun i=>summit _ a (hT i) (hS i)) (fun j k hj hp' _=> rivals (hp j k (Or.inl hj) hp')); obtain ⟨A,hA,b,W'⟩:= w.carts.left.zeal; convert warm (warm heH he') hZ using 1 <;> try rfl
    funext i
    obtain ⟨s,C,hs,H⟩:=(hT i).health (o i) e r; obtain ⟨s',C',hs',H'⟩:=(hS i).health (o i) e r
    simp only [Z,x,v,z,Pi.sub_apply]; rw [← axe_cut (T i e r) (S i e r) (graded F L i) (V i) K (o i) (penn_shrink H hs.le) (penn_shrink H' hs'.le) (strip_mono (W' i) (w.pay.output i).le le_rfl) (b i)];abel
end YM.FormalBulk08.Sierra
