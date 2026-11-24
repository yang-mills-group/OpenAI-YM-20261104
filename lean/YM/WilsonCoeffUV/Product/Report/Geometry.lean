import YM.WilsonCoeffUV.Product.Report.Census
/-!
# Progress of UV prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {m N M b d v u:ℕ}{H:Hol G}{F:Frame G h}{T:SectionData F}{E W V':Credit}{p:h<D}
-- normalized master at measurement m

def polarP (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m i:ℕ)(v:Verse F): TowerS G D:= Shrine (Peaks A Ñ T p N i) (steep A Ñ T p N m (i-m) v)
lemma tournure (R:Theatre H T p e E W)(V: Verse F)(t:R.V.anchor ≤ i)(v:i≤ N): On h (polarP R.V.draws R.V.paid T p N m i V):= Shrine_on _ (production R v t).1 _ le_rfl
lemma summerUp (L:Theatre H T p e E W)(V: Verse F)(v:L.V.anchor ≤ m)(t:m ≤ i)(q:i<N): Spout L.V.draws L.V.paid N i h h (polarP L.V.draws L.V.paid T p N m (i+1) V) = polarP L.V.draws L.V.paid T p N m i V:=by
    unfold polarP; rw [emptied L.V.draws L.V.paid L.V.hG L.V.green q (leaseN L (v.trans t) q) _ (production L (show i+1≤N from q) (v.trans (t.trans (by omega)))).1 le_rfl]; congr 1
    have he:= steep_height L (i:=i-m) V v (show m+(i-m+1) ≤N by omega); rw [show m+(i-m)=i by omega] at he; rw [show i+1-m=i-m+1 by omega]; exact he
lemma steep_nil (L:Theatre H T p e E W)(v:L.V.anchor≤m)(q:m≤N)(T': Verse F): polarP L.V.draws L.V.paid T p N m m T'= Shrine (L.lore N m) T':=by
    have he:= Street_up (i:=0) L T' v q; rw [street_nil] at he; rw [polarP,Nat.sub_self,he]

lemma agesQuote (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W V':Credit): ∃ C:Credit,∀ L:CourseS H T p e E W V',∀ (X Y:Verse F)(A δ:ℝ),0≤A → L.cab≤δ → (∀ i ≤ e,∀ j,twain A δ (coeff i (X j)) (coeff i (Y j))) →∀ i≤ e, ∀ j,
   let V:=L.vols; twain (C.buy L.Age*A) δ (coeff i (steep V.draws V.paid T p L.I.n L.spur L.length X j)) (coeff i (steep V.draws V.paid T p L.I.N L.spur L.length Y j)):=by
   obtain ⟨R,hR⟩:= SeasonM e H T p E W V'; obtain ⟨Q,H⟩:= SeasonC e H T p E W V'
   let X:ℝ:=(e+1:ℕ)*2*(∑ _ : Alma F,(e+1:ℕ)*(2:ℝ)); let T':= (pur X).prodC (R.prodC Q); refine ⟨T',fun V P Y A δ hx hy g i e' j=>?_⟩; intro S
   let Z:= V.Age; let t n:=bindingS S.draws S.paid T p n V.spur V.length false; let s n:= relativeC S.draws S.paid n V.spur V.length; have hp:1≤Z:=V.I.warm; have ht:0≤δ:=(trail_pos ..).le.trans hy
   have h h (a:h≤e)(l): twain ((∑ _ : Alma F,(e+1:ℕ)*(2*R.buy Z*(1:ℝ)))*A) δ (coeff h ((t V.I.n *ᵥ P) l)) (coeff h ((t V.I.N *ᵥ Y) l)):= cargo_rise _ _ _ 1 _ hx (zero_le_one.trans (R.purchase hp)) zero_le_one ht (fun h a i j=> (hR V h a i j).wide hy) _ _ (fun h a i=>by rw [one_mul]; exact g h a i) h a _
   let M:= R.buy Z; let L:=Q.buy Z; have hM:0≤M:=zero_le_one.trans (R.purchase hp); have hL:0≤L:=zero_le_one.trans (Q.purchase hp)
   let T0:=∑ _ : Alma F,(e+1:ℕ)*(2*M*(1:ℝ)); have h0:0≤T0:=Finset.sum_nonneg fun _ _=>by positivity
   apply (musicFund (s V.I.n) (s V.I.N) L T0 _ hx hL h0 ht (fun i j h g=>(H V i j h g).wide hy) _ _ h i e' j).lift _ ht; unfold T'; rw [Credit.products,Credit.products]; apply mul_le_mul_of_nonneg_right _ hx
   apply le_trans _ (mul_le_mul_of_nonneg_right (pure_goal _ _) (mul_nonneg hM hL)); unfold T0 X; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact le_of_eq (by unfold M L Z; ring)

def Compar (L:Schedule)(y:ℕ→ℝ)(m i:ℕ):ℝ:= y m+(L.scale i-L.scale m)+((i-m:ℕ):ℝ)
lemma polarBill (H:Hol G)(T:SectionData F)(p:h<D)(e u:ℕ)(E W V':Credit): ∃ C:Credit,∀ (L: ChorusLine H T p e E W V')(m i b N M:ℕ) (X Y: Verse F) (A δ Z:ℝ), L.arch.V.anchor ≤ m → m ≤ i → i≤ b → b ≤ M→ b ≤ N→ Compar L.arch.V.draws.S L.arch.V.y m i≤ Z →0≤A → L.arch.V.tempC i b≤ δ→ (∀ i ≤ e,∀ j,twain A δ (coeff i (X j)) (coeff i (Y j))) →
    ∀ j≤e,∀ r, let V:=L.arch.V; YieldP 0 1 u (C.buy Z*A) δ ((polarP V.draws V.paid T p N m i X).2 j r) ((polarP V.draws V.paid T p M m i Y).2 j r):=by
   obtain ⟨V,hV⟩:= agesQuote H T p e E W V'; obtain ⟨R,hR⟩:= Creed_more H T p e u E W
   let U:ℝ:= ((Fintype.card (Alma F)*(e+1):ℕ):ℝ)*2; let C:= (pur U).prodC (R.prodC V)
   refine ⟨C,fun L m i b N M X Y A δ Z hm hi hv hp hz x hy ht h j hj r=>?_⟩; intro s
   let Q: CourseS H T p e _ _ _:=⟨L,⟨s,m,i-m,N,M,b,hm,(by omega),hz,hp⟩,rfl⟩
   have H: Q.cab=s.tempC i b:=by unfold CourseS.cab WindowS.cab Q; dsimp only; rw [Nat.add_sub_of_le hi];
   have hy': Q.Age≤Z:=by unfold CourseS.Age WindowS.Age Q; dsimp only; rw [Nat.add_sub_of_le hi]; exact x
   have hb:s.anchor ≤ i:=hm.trans hi; have hx:s.y i≤Z:= (le_trans (show s.y i≤Q.Age from by
        have hQ : s.y (m+(i-m))≤ Q.Age:= Q.I.covers (le_refl Q.I.span); rwa [Nat.add_sub_of_le hi] at hQ) hy'); have ha:1≤Z:=Q.I.warm.trans hy'; have h' :0≤δ:= (trail_pos ..).le.trans ht
   have he l (u:l≤e) j:twain (V.buy Z*A) δ (coeff l (steep s.draws s.paid T p N m (i-m) X j)) (coeff l (steep s.draws s.paid T p M m (i-m) Y j)):= (hV Q X Y A δ hy (H.symm ▸ ht) h l u j).lift (mul_le_mul_of_nonneg_right (V.elder Q.I.warm hy') hy) h'
   have hf :0≤ V.buy Z:=zero_le_one.trans (V.purchase ha); have hf':0≤ R.buy Z:=zero_le_one.trans (R.purchase ha)
   unfold polarP; apply (tenderPV (L.arch.lore N i) (L.arch.lore M i) e r (R.buy Z) he (fun l v b'=>((hR L.arch i b N M l hb hv hz hp v b' r).expand ht).step (R.elder (s.depth _ hb) hx) h') hf' (mul_nonneg hf hy) h' hj).step _ h'
   apply le_trans _ (mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right (pure_goal U Z) (mul_nonneg hf' hf)) (le_of_eq (show _=C.buy Z by unfold C; rw [Credit.products,Credit.products]))) hy); unfold U; exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Mer
