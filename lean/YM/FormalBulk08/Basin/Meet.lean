import YM.FormalBulk08.Basin.Rod
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {τ:Time X}{J V:X→Type*}{T P:∀ i:X,J i→Tile (V i) (r+1)}{U S:∀ i:X,J i→Tile (V i) (m+1)}{b g c:∀ i,J i→ℝ}{q Q:∀ i:X,V i→V i→ℝ}{f:∀ i:X,Reach (V i)}{η δ p:X→ℝ}{x y:∀ i,J i→ V i}
-- estimate for ANY parameter p of polynomial reservoir. b might be Poly.p

def Chasm (τ:Time X)(f:∀ i,Reach (V i))(s:X→ℝ)(x y:∀ i,J i→V i)(b:∀ i,J i→ℝ):Prop:= ∃ A:X→ℝ,Soft τ A ∧ (∀ i,0≤ A i) ∧∀ i p, Real.exp (-s i /2 * (f i).d (x i p) (y i p)) ≤ A i*b i p
lemma bedrock (h: ∃ C:X→ℝ,Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ i, Grate (f i) (η i) (q i) (C i*p i))(hs:∀ i,0≤η i)(hv:Bear τ f x η b T)(ht:Bear τ f y η c U)(hp:Chasm τ f η x y g): Bear τ f x (fun i=>η i/2) (fun i j=> b i j*c i j * g i j*p i) (fun i j=> Lava.bond (q i) (T i j) (U i j)):= by
    obtain ⟨B,hB,V,L⟩:= hv; obtain ⟨A,hA,E,P⟩:= ht;obtain ⟨D,hD,M,H⟩:= hp; obtain ⟨C,hC,v,Q⟩:=h; let K:ℝ:= 1/2*(r+1)*(m+1); have hK:0≤K:=by unfold K;positivity
    refine ⟨_,(hD.times hC).times ((soft_coin τ K).times (hB.times hA)),fun i=>mul_nonneg (mul_nonneg (M i) (v i)) (mul_nonneg hK (mul_nonneg (V i) (E i))),fun i j=>?_⟩; refine ((pi_charge (f i) _ _ (L i j) (P i j) (Q i) (hs i)).bill).mono ?_; refine (mul_le_mul_of_nonneg_right (H i j) (mul_nonneg (mul_nonneg (mul_nonneg (show 0≤K from hK) (L i j).1) (P i j).1) (Q i).1)).trans_eq ?_; unfold K;ring
lemma haul (h:Aster.Silver τ f η q)(hs:∀ i,0≤η i)(hv:Bear τ f x η b T)(ht:Bear τ f y η c U)(hp:Chasm τ f η x y g) : Bear τ f x (fun i=>η i/2) (fun i j=> b i j*c i j * g i j) (fun i j=> Lava.bond (q i) (T i j) (U i j)):= by
    obtain ⟨v,C,c,X⟩:=h; have hZ := bedrock (p:=fun _=>1) (q:=q) ⟨C,c,fun i=>(X i).1,fun i=>by rw [mul_one];exact X i⟩ hs hv ht hp; simpa only [mul_one] using hZ
lemma havoc (h:Gilt τ f η δ q Q)(hs:∀ i,0≤η i)(hv:Matched τ f x η δ b T P)(ht: Matched τ f y η δ c U S)(hp:Chasm τ f η x y g): Matched τ f x (fun i=>η i/2) δ (fun i j=>b i j*c i j*g i j) (fun i j=>Lava.bond (q i) (T i j) (U i j)) (fun i j=> Lava.bond (Q i) (P i j) (S i j)):= by
   have hh : Bear τ f x (fun i=>η i/2) (fun i j=>δ i*(b i j*c i j*g i j)) (fun i j=> Lava.bond (q i-Q i) (P i j) (S i j)):= by
       convert bedrock h.haze hs hv.right ht.right hp using 1; apply funext;intro i; ext j; ring
   have he: Bear τ f x (fun i=>η i/2) (fun i j=>δ i*(b i j*c i j*g i j)) (fun i j=> Lava.bond (q i) (T i j-P i j) (U i j)):= by convert haul h.left hs hv.chalk ht.left hp using 1; apply funext;intro i; ext j;ring
   have hQ: Bear τ f x (fun i=>η i/2) (fun i j=>δ i*(b i j*c i j*g i j)) (fun i j=> Lava.bond (q i) (P i j) (U i j-S i j)):= by convert haul h.left hs hv.right ht.chalk hp using 1;apply funext; intro i;ext j;ring
   obtain ⟨C,c₁,u,V'⟩:= hv.left; obtain ⟨Z,z,u',X⟩:= hv.right; obtain ⟨A,c₂,a,W⟩:= ht.left; obtain ⟨B,c₃,a',Y⟩:=ht.right
   obtain ⟨s,G,x',M⟩:=h.left; obtain ⟨w,H,y',K⟩:= h.right; obtain ⟨E,l,e,F⟩:=h.haze
   have H1 i (a b: V i) : (q i-Q i) a b=(q i-Q i) b a:= congr_arg₂ (fun x y:ℝ=>x-y) (s i a b) (w i a b)
   refine ⟨haul h.left hs hv.left ht.left hp, haul h.right hs hv.right ht.right hp,?_⟩; convert (he.plus hQ).plus hh using 1; funext i j
   exact grates_diff (penn_bail (V' i j) (hs i)) (penn_bail (X i j) (hs i)) (W i j) (Y i j) ((M i).turn (s i)) ((K i).turn (w i)) ((F i).turn (H1 i)) (hs i)
lemma huddle {P:∀ i:X,J i→Waves (V i)}{R Z U:∀ i:X,J i→ Waves (V i)}(h: Gilt τ f η δ q Q)(hs:∀ i,0≤η i)(hp:∀ i e r, e≤E →0<r → Matched τ f x η δ b (fun j p=>P j p i e r) (fun j p=>R j p i e r))(ht:∀ i e r,e≤E →0<r → Matched τ f y η δ c (fun j p=>Z j p i e r) (fun j p=> U j p i e r))(he: Chasm τ f η x y g) i e (hE:e≤E) m: Matched τ f x (fun i=>η i/2) δ (fun i j=>b i j*c i j*g i j) (fun j p=>brawl (q j) (P j p) (Z j p) i e m) (fun j p=>brawl (Q j) (R j p) (U j p) i e m):= by
   unfold brawl Lava.reach
   refine matched_sums _ (fun i hi=> matched_sums _ (fun j hj=> matched_sums _ (fun k hk=>?_))); simp_rw [visor_eq]
   rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi; exact ((havoc h hs (hp j.1 i.1 _ (by omega) (by omega)) (ht j.2 i.2 _ (by omega) (by omega)) he).polish).lengthen _
end YM.FormalBulk08.Basin
