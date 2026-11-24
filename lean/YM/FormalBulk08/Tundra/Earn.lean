import YM.FormalBulk08.Tundra.Sleet

/-! Polynomial relative charges on deterministic transmissions. Entries
marked by inherited roots independent. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I : Type} {V W:X→Type}{U:X→Type*}{u m n:ℕ}{τ:Time X} {σ δ:X→ℝ} {ε θ:X→ℝ≥0}
variable {P Q:∀ i:X, Row (V i) (W i)} {f:∀ i:X,U i→ Biglot (V i)} {b:∀ i,U i→ℝ}{T S:∀ i:X,U i→Tile (Biglot (V i)) n} {L:X→Side}
def Whey (u:ℕ)(τ:Time X)(f:∀ i:X,U i→Biglot (V i))(ε:X→ℝ≥0)(b:∀ i,U i→ℝ)(T:∀ i:X,U i→Tile (Biglot (V i)) n) := Bear τ (fun i=> grain (fame _) (ε i)) f (fun _=>u) b T
def Lacy (u:ℕ)(τ:Time X)(f:∀ i:X,U i→ Biglot (V i))(ε:X→ℝ≥0)(δ:X→ℝ)(b:∀ i,U i→ℝ)(T S:∀ i:X,U i→Tile (Biglot (V i)) n):= Matched τ (fun i=>grain (fame _) (ε i)) f (fun _=>u) δ b T S
lemma colder (h:Whey u τ f θ b T)(hb:∀ i, ε i≤1)(he:∀ i,ε i≤(L i).val*θ i) : Whey u τ (fun i p=> Bank.scroll (L i) _ (f i p)) ε b (fun i p=> jetty (Bank.scroll (L i) _).symm (T i p)):= by
    obtain ⟨A,a,w,H⟩:=h; let C:= Real.exp ((u:ℝ)*plum 1 8); refine ⟨_,(soft_coin τ C).times a,fun i=>mul_nonneg (Real.exp_pos _).le (w i),fun i p=>?_⟩; rw [mul_assoc]; exact flipping (T i p) _ (hb i) (he i) (by rw [Equiv.symm_apply_apply]; exact H i p)
lemma colder_way (h:Lacy u τ f θ δ b T S)(hb:∀ i, ε i≤1)(he:∀ i, ε i≤(L i).val*θ i): Lacy u τ (fun i p=> Bank.scroll (L i) _ (f i p)) ε δ b (fun i p=>jetty (Bank.scroll (L i) _).symm (T i p)) (fun i p=>jetty (Bank.scroll (L i) _).symm (S i p)):= ⟨colder h.1 hb he,colder h.2 hb he,colder h.3 hb he⟩
lemma colden {T:∀ x:X,U x→ Tile (Biglot (W x⊕ V x)) m}(h:Whey u τ (fun i p=> coastRight _ _ _ (f i p)) θ b T): Whey u τ f θ b (fun i p=>jetty (coastRight _ _ _) (T i p)):= by
   obtain ⟨C,c,v,H⟩:=h; refine ⟨C,c,v,fun i p=> cut_charge (W:=grain (fame (W i⊕ V i)) (θ i)) (f:=coastRight Cover (W i) (V i)) ?_ (fun _ _=> rfl) _ (H i p)⟩; intro a b hv; exact Prod.ext (show (coastRight _ _ _ a).1=(coastRight _ (W i) _ b).1 from congr_arg Prod.fst hv) (Sum.inr_injective (show (coastRight _ (W i) _ a).2=(coastRight _ _ _ b).2 from congr_arg Prod.snd hv))
lemma colds {T S:∀ x:X,U x→Tile (Biglot (W x⊕ V x)) m}(h:Lacy u τ (fun i p=>coastRight _ _ _ (f i p)) θ δ b T S): Lacy u τ f θ δ b (fun i p=>jetty (coastRight _ _ _) (T i p)) (fun i p=>jetty (coastRight _ _ _) (S i p)):= ⟨colden h.1,colden h.2,colden h.3⟩
variable [∀ i,Fintype (V i)] [∀ i,Fintype (W i)]
lemma garlands (h:Whey u τ f ε b T)(ht:ease τ σ P)(hc:Soft τ (fun i=> (σ i)⁻¹))(he:∀ i, ε i≤1)(hs:∀ i,0<σ i)(hw:Soft τ (fun i=> (Fintype.card (W i):ℝ)))(y:∀ i:X,U i→ W i): Whey u τ (fun i p=> ((f i p).1,y i p)) ε b (fun i p=> pearl (lands (P i)) (T i p)):= by
    obtain ⟨C,c,v,H⟩:=h; obtain ⟨A,a,Y,M⟩:=ht; refine ⟨_, c.times (((sackSoft u hc).times (hw.times a)).pows n),fun i=>mul_nonneg (v i) (pow_nonneg (mul_nonneg (sack_pos _ (hs i)) (mul_nonneg (Nat.cast_nonneg _) (Y i))) _),fun i p=>?_⟩; have hP:= (school (fun _:Fin n=>P i) _ (f i p) (y i p) (fun _=> A i) (H i p) (hs i) (he i) (fun _=> M i) (fun _=>Y i)).bill; apply Knoxville.mono hP; rw [one_mul, Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_right_comm]
lemma freezeL (h:Lacy u τ f ε δ b T S)(ht:Maori τ σ δ P Q)(hc:Soft τ (fun i=> (σ i)⁻¹))(he:∀ i,ε i≤1)(hs:∀ i,0<σ i)(hw:Soft τ (fun i=>(Fintype.card (W i):ℝ)))(hd:∀ i,0≤δ i)(y:∀ i:X,U i→ W i): Lacy u τ (fun i p=> ((f i p).1,y i p)) ε δ b (fun i p=> pearl (lands (P i)) (T i p)) (fun i p=>pearl (lands (Q i)) (S i p)):= by
    obtain ⟨A,a,v,Z⟩:=h.left; obtain ⟨C,c,w,H⟩:=h.right
    obtain ⟨K,k,r,U⟩:=ht.left; obtain ⟨D,d,u',V⟩:=ht.right; obtain ⟨G,g,Y,M⟩:=ht.lamp
    have hx : Whey u τ (fun i p=> ((f i p).1,y i p)) ε (fun i p=>δ i*b i p) (fun i p=>pearl (lands (P i)) (S i p)-pearl (lands (Q i)) (S i p)):= by
       refine ⟨_,(soft_coin τ (n:ℝ)).times ((c.times (((sackSoft u hc).times hw).pows n)).times (g.times ((k.plus d).pows (n-1)))),fun i=>mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (w i) (pow_nonneg (mul_nonneg (sack_pos _ (hs i)) (Nat.cast_nonneg _)) _)) (mul_nonneg (Y i) (pow_nonneg (add_nonneg (r _) (u' _)) _))),fun i p=>?_⟩
       apply Knoxville.mono (chase (strip_mono (U i) le_rfl (le_add_of_nonneg_right (u' i))) (strip_mono (V i) le_rfl (le_add_of_nonneg_left (r i))) (M i) (hs i) (add_nonneg (r i) (u' i)) (mul_nonneg (Y i) (hd i)) (he i) (y i p) (H i p)); apply le_of_eq;ring
    refine ⟨garlands h.left ht.left hc he hs hw y,garlands h.right ht.right hc he hs hw y,?_⟩
    convert Bear.plus (garlands h.chalk ht.left hc he hs hw y) hx using 1; funext i p; rw [← haggle (y i p) (petris (Z i p)) (petris (H i p)) (strip_mono (U i) (hs i).le le_rfl) (r i) le_rfl,sub_add_sub_cancel]
end YM.FormalBulk08.Tundra
