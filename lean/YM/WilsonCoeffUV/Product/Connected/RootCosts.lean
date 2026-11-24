import YM.WilsonCoeffUV.Product.Connected.Carried
/-!
# Anchored flux prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
section
variable {I:Type*}{J:I→Type*}{α:I→Type*}{p:(i:I)→J i→ ProfileW}{x θ y:(i:I)→J i→ℝ}
structure RampR {I:Type*}{J:I→Type*}(p:(i:I)→ J i→ ProfileW)(x θ y:(i:I)→J i→ℝ):Prop where
    he:∀ i j, AngleSea (p i j)
    widthS : ∀ i,Brite (x i) (θ i)
    tariff : 0≤y
abbrev Porch (p:(i:I)→J i→ ProfileW)(x θ y:(i:I)→J i→ℝ)(u:ℕ)(P Q:(i:I)→ J i→ Ten ℝ (Cloth (α i)) r):Prop:= ∃ d:ℕ,∀ i,∃ C:ℝ,0≤ C∧∀ j,PromX (p i j) u (C*x i j^d*y i j) (θ i j) (P i j) (Q i j)
variable {P Q U V:(i:I)→ J i→ Ten ℝ (Cloth (α i)) r}
lemma Porch.add (h:Porch p x θ y u P Q)(q: Porch p x θ y u U V)(v:RampR p x θ y): Porch p x θ y u (P+U) (Q+V):=by
   obtain ⟨d,H⟩:=h; obtain ⟨e,X⟩:=q; refine ⟨d+e,fun i=>?_⟩; obtain ⟨A,a,Y⟩:= H i; obtain ⟨B,b,Z⟩:= X i
   refine ⟨A+B,add_nonneg a b,fun j=>?_⟩; exact ((Y j).add (Z j)).stepX (by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (roof_pair _ _ _ ((v.widthS i).large j) a b _ _) (v.tariff i j)) ((v.widthS i).dist j)
lemma Porch.sum {S:Finset ι}{P Q:ι→ (i:I)→ J i→ Ten ℝ (Cloth (α i)) r}(h:∀ i∈ S,Porch p x θ y u (P i) (Q i))(v:RampR p x θ y): Porch p x θ y u (fun i j=>∑ n∈ S,P n i j) (fun i j=>∑ n∈ S,Q n i j):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact ⟨0,fun _=>⟨0,le_rfl,fun j=> by rw [zero_mul,zero_mul]; exact PromX.zero⟩⟩
    | @insert i S e ih=> simp_rw [Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj)) v
lemma Porch.μ (h:Porch p x θ y u P Q)(c:ℝ): Porch p x θ y u (fun i j=>c • P i j) (fun i j=> c • Q i j):= by obtain ⟨n,H⟩:=h; refine ⟨n,fun i=>?_⟩; obtain ⟨A,hp,p⟩:=H i; exact ⟨‖c‖*A,by positivity,fun j=> by rw [mul_assoc,mul_assoc ‖c‖]; convert! (p j).μ c using 1; ring⟩
end
section
variable {Y:Gear G→Type*}{p:(i:Gear G)→ Y i→ ProfileW}{T:(i: Gear G)→ Y i→ Rally (e+1) 0 i}{y:(i:Gear G)→ Y i→ℝ}
variable (p y)(X Z:(i:Gear G)→ Y i→ Pal ℝ (Cloth (Helms i)))
lemma northX (w:RampR p (xpos e T) (dpos e T) y){X Z:(i:Gear G)→ Y i→ Layers ℝ (Cloth (Helms i))} (P Q:(i:Gear G)→Y i→ ropes Cover (Helms i) (Helms i)) (q:∀ i j,Ballast i.σ i.D (dpos e T i j) (P i j) (Q i j))(hv:i≤e) (f: ∀ v≤k,∀ j≤ i',∀ r, Porch p (xpos e T) (dpos e T) y u (fun I v'=>X I v' v j r) (fun I v'=>Z I v' v j r))(hi:i≤ i')(r:ℕ): Porch p (xpos e T) (dpos e T) y u (fun I v=>Soil.paintC (P I v) ((T I v).P.rays) (X I v) k i r) (fun I v=> Soil.paintC (Q I v) ((T I v).Q.rays) (Z I v) k i r):=by
    simp_rw [Soil.paintC,Finset.sum_apply]; apply Porch.sum _ w; intro j hj; apply Porch.sum _ w; intro a ha; have he:=Finset.mem_antidiagonal.mp hj; have h':=Finset.mem_antidiagonal.mp ha; simp_rw [rondel]; apply Porch.sum _ w; intro b hb; have hx:= Finset.mem_antidiagonal.mp hb
    obtain ⟨d,H⟩:= Satin.flywheel (G:=G) j.1 a.1 (b.1+1) (e+1) 0 (Or.inl (by omega)) Gear.σ Gear.holds (fun I=> I.price.le)
    obtain ⟨n,F⟩:= f j.2 (by omega) a.2 (by omega) (b.2+1); refine ⟨n+d,fun I=>?_⟩; obtain ⟨A,x,g⟩:=F I; obtain ⟨C,h,t⟩:= H I; let V:=tender (Helms I) I.σ u; let R:=piped (Helms I) b.1 I.σ u; have hh:=zero_le_one.trans I.bill_nn
    refine ⟨3*pegPrice b.1 b.2*(A*((I.D*V)*(C*R))),?_,fun j=>?_⟩
    · have hu:0≤pegPrice b.1 b.2:= by unfold pegPrice; positivity
      have hV:0≤V:= tender_nn I.price ..; have hR:0≤R:= piped_nn b.1 I.price u; positivity
    have hw:= (g j).raft2 (t (T I j)) (q I j) I.price (w.he I j) hx; rw [pow_add]; convert! hw using 1; unfold V R xpos largus; ring
lemma sod (w:RampR p (xpos e T) (dpos e T) y) (q:i≤e) (f:∀ j,∀ l≤j', Porch p (xpos e T) (dpos e T) y u (fun I v=> X I v l j) (fun I v=> Z I v l j)) (hq:i≤j')(r k:ℕ): Porch p (xpos e T) (dpos e T) y u (fun I v=>heap ((T I v).P.payMat) ((T I v).P.rays) (X I v) k i r) (fun I v=> heap ((T I v).Q.payMat) ((T I v).Q.rays) (Z I v) k i r) :=by
   induction k using Nat.strong_induction_on generalizing r i with
   | h k ih=>
     cases k with
     | zero=> simp_rw [level]; exact f r i hq
     | succ k=>
       let Q I v:=(T I v).P.payMat; let Z' I v:= (T I v).Q.payMat; have hM I v:= (pm_rate (T I v)).mono I.holds.le
       let P' I v:= heap (Q I v) ((T I v).P.rays) (X I v); let T' I v:= heap (Z' I v) ((T I v).Q.rays) (Z I v)
       have hv a (h:a≤ k) j (t:j≤ i) r:Porch p (xpos e T) (dpos e T) y u (fun I v=>P' I v a j r) (fun I v=>T' I v a j r):= ih a (by omega) (t.trans q) (t.trans hq) r
       have ht:= northX p y w Q Z' hM q hv le_rfl r; have h':= northX p y w (fun i v=>(Q i v).transpose) (fun i v=>(Z' i v).transpose) (fun i v=> Cosmos.BankT (hM ..)) q hv le_rfl r
       have hy : Porch p (xpos e T) (dpos e T) y u (fun I v=> rime (Q I v) (P' I v k i) r) (fun I v=> rime (Z' I v) (T' I v k i) r):=by
          obtain ⟨n,H⟩:= hv k le_rfl i le_rfl (r+2); refine ⟨n,fun I=>?_⟩; obtain ⟨A,h,X⟩:=H I
          refine ⟨2*I.D*fareV r*A,mul_nonneg (by have hh:= zero_le_one.trans I.bill_nn; unfold fareV; positivity) h,fun j=>?_⟩
          convert! (X j).raft1 (hM I j) I.price using 1; ring
       simp only [inchC,Pi.smul_apply]; exact ((hy.add ht w).add h' w).μ _
lemma panelX (W Z:(i:Gear G)→ Y i→ Bookend ℝ G)(i j:ℕ) (v:RampR p (xpos e T) (dpos e T) y)(f: Porch (fun i j u=> p i j (parentC i.patch.L u)) (xpos e T) (dpos e T) y u (fun I v=> W I v i j) (fun I v=>Z I v i j)) : Porch p (xpos e T) (dpos e T) y u (fun I v=>slidesJ I.patch (T I v).P.Q (W I v) i j) (fun I v=>slidesJ I.patch (T I v).Q.Q (Z I v) i j):=by
   obtain ⟨d,H⟩:= f; refine ⟨d,fun I=>?_⟩; obtain ⟨A,a,h⟩:=H I; have hx:= tender_nn (I.price.trans I.holds) (Helms I) u; have hy:= zero_le_one.trans I.bill_nn
   refine ⟨(j+1:ℕ)*((I.D*tender (Helms I) I.s u)^j*A),by positivity,fun w=>?_⟩
   let X:= tiles I.patch.L (W I w i); let F:= tiles I.patch.L (Z I w i); let j':= T I w
   have hp: PromX (p I w) u (A*(xpos e T I w)^d*y I w) j'.σ (X j) (F j):=⟨portStand (P:=W I w i) (h w).paid,portStand (P:=Z I w i) (h w).feud, portStand (P:=W I w i-Z I w i) (h w).dropR⟩
   have ht:= hp.rafts (v.he I w) (I.price.trans I.holds) (votes I (T I w)); convert! ht using 1; unfold Helms; ring
lemma sodRoots (W Z:(i:Gear G)→ Y i→ Bookend ℝ G)(v:RampR p (xpos e T) (dpos e T) y)(q:i≤e) (f: ∀ j,∀ l≤ i', Porch (fun i j u=> p i j (parentC i.patch.L u)) (xpos e T) (dpos e T) y u (fun I v=> W I v l j) (fun I v=>Z I v l j))(hv:i≤ i')(r k:ℕ): Porch p (xpos e T) (dpos e T) y u (fun I v=> Pcross I (T I v).P (W I v) k i r) (fun I v=> Pcross I (T I v).Q (Z I v) k i r):= sod p y _ _ v q (fun j i t=> panelX _ _ _ _ i j v (f j i t)) hv r k
end
end YM.WilsonCoeffUV.Mer
