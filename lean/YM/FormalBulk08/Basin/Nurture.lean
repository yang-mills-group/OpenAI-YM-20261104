import YM.FormalBulk08.Basin.Meet
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {τ:Time X}{J V:X→Type*}{b g c:∀ i,J i→ℝ}{f:∀ i:X,Reach (V i)}{η δ:X→ℝ}{x y:∀ i,J i→ V i}
lemma cave_b {T:∀ i:X,J i→ Tile (V i) r}{S:∀ i:X,J i→Tile (V i) m}(hs:∀ i,0≤η i)(h:Bear τ f x η b T)(hp:Bear τ f x η c S): Bear τ f x η (fun i j=> b i j*c i j) (fun i j=>clutch (T i j) (S i j)):= by
   obtain ⟨C,z,p,H⟩:=h; obtain ⟨B,c,u,Q⟩:=hp; refine ⟨_,z.times c,fun i=> mul_nonneg (p i) (u i),fun i j=>?_⟩; convert clasp_cash (H i j) (Q i j) (hs i) using 1;ring
lemma metabolic {T Q:∀ i:X,J i→ Tile (V i) r}{S Z:∀ i:X,J i→Tile (V i) m}(hs:∀ i,0≤η i)(h:Matched τ f x η δ b T Q)(hp:Matched τ f x η δ c S Z): Matched τ f x η δ (fun i j=> b i j*c i j) (fun i j=>clutch (T i j) (S i j)) (fun i j=>clutch (Q i j) (Z i j)):= by
   have ht:= cave_b hs h.chalk hp.left; have hu:= cave_b hs h.right hp.chalk
   refine ⟨cave_b hs h.left hp.left,cave_b hs h.right hp.right,?_⟩; have hz:(fun i j=> b i j*(δ i*c i j))=(fun i j=>δ i*b i j*c i j):= funext fun i=>funext fun j=>(by ring); rw [hz] at hu; convert ht.plus hu using 1; · apply funext;intro i; ext j;ring
   funext i p v; simp only [Pi.sub_apply,Pi.add_apply,clutch];ring
lemma neatpack {T Q S Z:∀ i:X,J i→ OrbitV (V i)}(hs:∀ i,0≤η i)(h:∀ j r,j≤E→Matched τ f x η δ b (fun i p=>T i p j r) (fun i p=> Q i p j r))(hp:∀ j r,j≤E→ Matched τ f x η δ c (fun i p=>S i p j r) (fun i p=>Z i p j r))(e r)(he:e≤ E): Matched τ f x η δ (fun i j=>b i j*c i j) (fun i p=>duplexB (T i p) (S i p) e r) (fun i p=>duplexB (Q i p) (Z i p) e r):=by
   unfold duplexB diplex; apply matched_sums; intro i hi; apply matched_sums; intro j _; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi; exact ((metabolic hs (h i.1 j.val.1 (by omega)) (hp i.2 j.val.2 (by omega))).polish).lengthen _
lemma curr {T Q S Z:∀ i:X,J i→ Waves (V i)}(hs:∀ i,0≤η i)(h:∀ k j r,j≤E→Matched τ f x η δ b (fun i p=>T i p k j r) (fun i p=> Q i p k j r))(hp:∀ k j r,j≤E→ Matched τ f x η δ c (fun i p=>S i p k j r) (fun i p=>Z i p k j r))(t e r)(he:e≤ E): Matched τ f x η δ (fun i j=>b i j*c i j) (fun i p=>doubled (T i p) (S i p) t e r) (fun i p=>doubled (Q i p) (Z i p) t e r):=by unfold doubled; apply matched_sums; intro k hk; exact neatpack hs (h k.1) (hp k.2) e r he
lemma pearl_grade (τ:Time X) (f:∀ i,Reach (V i))(η:X→ℝ)(x:∀ i,J i→ V i)(e r): Bear τ f x η (fun _ _=>1) (fun i _=>bead (V i) e r):=by
   by_cases he:e+r=0
   · obtain rfl:e=0:= (by omega); obtain rfl:r=0:= (by omega); refine ⟨_,soft_coin τ 1,fun _=>zero_le_one,fun i p=> ⟨?_,?_⟩⟩
     · norm_num
     have hp (u:chain (V i) 1):wide (f i) u=0:= Nat.eq_zero_of_le_zero (known_wide _ _ 0 (fun a b=>by simp only [Subsingleton.elim a b,(f i).self,le_refl]))
     simp [Gorge.shine,hp,bead]
   have hx i: (bead (V i) e r)=0:= by funext j; exact if_neg he
   simp_rw [hx]; apply bear_void
lemma pearl_fare (τ:Time X) (f:∀ i,Reach (V i))(η:X→ℝ)(x:∀ i,J i→ V i)(t e r): Bear τ f x η (fun _ _=>1) (fun i _=> pebbleW (V i) t e r) := by
   by_cases he:t=0
   · simp only [pebbleW,if_pos he];exact pearl_grade ..
   simp_rw [pebbleW,if_neg he]; exact bear_void τ _ x _ _ _
variable {b:I→∀ i:X,J i→ℝ}{Y Z: I→ ∀ i:X,J i → Waves (V i)}
def cartwork (L:List I)(b:I→∀ i:X,J i→ℝ)(i:X)(p:J i) := (L.map fun k=>b k i p).prod
lemma company (hs:∀ i,0≤η i)(L:List I)(h:∀ i∈L,∀ j e r,e≤ E→ Matched τ f x η δ (b i) (fun p q=>Y i p q j e r) (fun p q=>Z i p q j e r)) j e r (he:e≤ E): Matched τ f x η δ (cartwork L b) (fun i p=> campfire (fun k=>Y k i p) L j e r) (fun i p=> campfire (fun k=> Z k i p) L j e r):= by
   induction L generalizing j e r with
   | nil=> exact Matched.constant (pearl_fare _ _ _ _ _ _ _)
   | cons i l ih=>exact curr hs (h i List.mem_cons_self) (fun j e r he=> ih (fun i hi=> h i (List.mem_cons_of_mem _ hi)) j e r he) j e r he
lemma backed {Y Z:I→∀ i:X,J i→OrbitV (V i)}(hs:∀ i,0≤η i)(L:List I)(h:∀ i∈L,∀ e r,e≤E→ Matched τ f x η δ (b i) (fun p q=>Y i p q e r) (fun p q=>Z i p q e r)) e r (he:e≤ E): Matched τ f x η δ (cartwork L b) (fun i p=>packV (fun k=>Y k i p) L e r) (fun i p=>packV (fun k=>Z k i p) L e r):= by
   induction L generalizing e r with
   | nil=>exact Matched.constant (pearl_grade _ _ _ _ _ _)
   | cons i l ih=> exact neatpack hs (h i List.mem_cons_self) (fun j k he=> ih (fun i hi=>h i (List.mem_cons_of_mem _ hi)) _ _ he) _ _ he
end YM.FormalBulk08.Basin
