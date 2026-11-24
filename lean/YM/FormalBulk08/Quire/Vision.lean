import YM.FormalBulk08.Quire.Cart
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X : Type}{U:X→ Type*}{r n m e:ℕ}{τ:Time X}{η δ:X→ℝ}{b:∀ i,U i→ℝ}
section
variable {Y Z:X→Type}[∀ i,Fintype (Y i)][∀ i,Fintype (Z i)]{P Q:∀ i:X,Row (Y i) (Z i)}{o:∀ i,U i→Biglot (Y i)}{T S:∀ i:X,U i→Tile (Biglot (Y i)) r}
lemma Bear.gift (ht: Bear τ (fun _=> fame _) o η b T)(he:∀ i,0≤η i)(hp:ease τ η P)(h:Soft τ (fun i=>(Fintype.card (Z i):ℝ)))(f:∀ i:X,U i→Z i): Bear τ (fun _=>fame _) (fun i p=>((o i p).1,f i p)) η b (fun i p=> pearl (lands (P i)) (T i p)):= by
   obtain ⟨C,c,u,H⟩:=ht; obtain ⟨A,a,hz,K⟩:=hp; refine ⟨_,c.times ((h.times a).pows r),fun i=>mul_nonneg (u i) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hz i)) r),fun i p=>?_⟩; apply Knoxville.mono (penn_pearl (P i) (o i p) (f i p) (H i p) (he i) (K i) (hz i)); rw [one_mul,mul_right_comm]
lemma Matched.gift (ht:Matched τ (fun _=> fame _) o η δ b T S) (he:∀ i,0≤η i)(hp:Maori τ η δ P Q)(h:Soft τ (fun i=>(Fintype.card (Z i):ℝ)))(hr:∀ i,0≤δ i)(f:∀ i:X, U i→ Z i) : Matched τ (fun _=>fame _) (fun i p=>((o i p).1,f i p)) η δ b (fun i p=> pearl (lands (P i)) (T i p)) (fun i p=> pearl (lands (Q i)) (S i p)):= by
   obtain ⟨C,c,u,H⟩:=hp.left; obtain ⟨D,d,s,M⟩:=hp.right; obtain ⟨G,g,w,K⟩:=hp.lamp; obtain ⟨A,a,ha,F⟩:= ht.left; obtain ⟨B,b',hb,U⟩:= ht.right
   have hc i:0≤C i+D i:= add_nonneg (u i) (s i)
   have hx : Bear τ (fun _=>fame _) (fun i p=> ((o i p).1,f i p)) η (fun i p=>δ i*b i p) (fun i p => pearl (lands (P i)) (S i p)-pearl (lands (Q i)) (S i p)):= by
       refine ⟨_,(soft_coin τ (r:ℝ)).times ((b'.times (h.pows r)).times (g.times ((c.plus d).pows (r-1)))),fun i=>mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (hb i) (pow_nonneg (Nat.cast_nonneg _) _)) (mul_nonneg (w i) (pow_nonneg (hc i) _))),fun i p=>?_⟩; convert hurray (f i p) (U i p) (he i) (strip_mono (H i) le_rfl (le_add_of_nonneg_right (s i))) (strip_mono (M i) le_rfl (le_add_of_nonneg_left (u i))) (K i) (hc i) (mul_nonneg (w i) (hr i)) using 1; ring
   refine ⟨ht.left.gift he hp.left h f,ht.right.gift he hp.right h f,?_⟩; convert (ht.chalk.gift he hp.left h f).plus hx using 1;funext i p; rw [←haggle (f i p) (F i p) (U i p) (H i) (u i) (he i),sub_add_sub_cancel]
lemma Bear.jet {Y Z:X→Type}{o:∀ i,U i→Biglot (Z i)}{T:∀ i:X,U i→ Tile (Biglot (Y i⊕Z i)) r}(h: Bear τ (fun _=>fame _) (fun i p=>coastRight _ _ _ (o i p)) η b T): Bear τ (fun _=>fame _) o η b (fun i p=>jetty (coastRight _ _ _) (T i p)):= by obtain ⟨C,c,u,H⟩:=h;exact ⟨C,c,u,fun i p=>penn_port (H i p)⟩
lemma Matched.jet {Y Z:X→Type}{o:∀ i,U i→ Biglot (Z i)}{T S:∀ i:X,U i→ Tile (Biglot (Y i⊕Z i)) r}(h: Matched τ (fun _=>fame _) (fun i p=> coastRight _ _ _ (o i p)) η δ b T S): Matched τ (fun _=> fame _) o η δ b (fun i p=>jetty (coastRight _ _ _) (T i p)) (fun i p=> jetty (coastRight _ _ _) (S i p)):= ⟨h.left.jet,h.right.jet,h.chalk.jet⟩
end
section
variable {Y:X→ Type*}{R:∀ i, Reach (Y i)}{o:∀ i,U i→Y i}{q Q:∀ i:X,Y i→Y i→ℝ}
lemma concentric (p i j:ℕ)(hG:Gilt τ R η δ q Q)(hs:∀ i,0≤η i){Z W:∀ x:X,OrbitV (Y x)}(hZ:∀ i,Fiery (Z i))(hW:∀ i,Fiery (W i)) {T S:∀ x:X,U x→OrbitV (Y x)}
    (hf:orbit_access e r i j p)(hp:∀ n i k,i≤ e→ 0<k→ Totem τ R η δ (fun x=>swim (q x) (Z x) n i k) (fun x=>swim (Q x) (W x) n i k))(he:∀ i j:ℕ,precede e r i j→Matched τ R o η δ b (fun x p=> T x p i j) (fun x p=> S x p i j)):
    Matched τ R o η δ b (fun x u=> dipper (q x) (swim (q x) (Z x)) (T x u) p i j) (fun x u=> dipper (Q x) (swim (Q x) (W x)) (S x u) p i j):= by
    induction p using Nat.strong_induction_on generalizing i j with
    | _ p ih=>
       cases p with
       | zero=> simp_rw [dipper_first]; unfold orbit_access at hf; exact he i j (Or.resolve_right hf (by omega))
       | succ n=>
          simp_rw [dipper_succ]; refine Matched.amp (Matched.plus ((ih n (by omega) i _ (prices_flow hf (by omega))).bake hs hG) (Matched.amp ?_ (Pact.coin ..))) (Pact.coin ..)
          unfold brawl Lava.reach; apply matched_sums _; intro l hl; apply matched_sums _; intro v hv; apply matched_sums _; intro w hw; rw [Finset.mem_antidiagonal] at hl hv; simp_rw [visor_eq]; apply Matched.lengthen; apply Matched.polish
          by_cases h:l.1=0
          · have hh (x:X)(n r): swim (q x) (Z x) n 0 r=0:= by by_contra ht;have hp:=(thermal (q x) (hZ _) _ _ _ ht).1;omega
            have hu (x:X)(n r): swim (Q x) (W x) n 0 r=0:= by by_contra ht;have hp:=(thermal (Q x) (hW _) _ _ _ ht).1;omega
            simp_rw [h,hh,hu,bond_void]; apply mates_void
          exact Matched.bond (hp _ _ _ (by unfold orbit_access precede at *;omega) (by omega)) (ih v.2 (by omega) _ _ (by unfold orbit_access precede at *;omega)) hG hs
end
end YM.FormalBulk08.Quire
