import YM.WilsonCoeffUV.Vacuum.Step.Ratio
/-!
# Price type for local post-length. Uniform exponent across vertices,
dimension/horizon fixed by call; G,kernel fixed or not is in type. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{i j ℓ n k r:ℕ}{σ A δ:ℝ} {I U J V:Type*}

section furl
variable [NormedAddCommGroup V] {α:I→Type*}{J:I→Type*}{x θ:(i:I)→ J i→ℝ}{s t:I→ℝ}
/-- tariff polynomial uniformly in arbitrary Gear/H list (dependent port shapes).
Leads chosen first even for Type valuations. -/
def Satin (x θ:(i:I)→ J i→ℝ)(s:I→ℝ)(P Q:(i:I)→ J i→ Ten V (Cloth (α i)) r) :=
    ∃ d:ℕ,∀ i:I,∃ C:ℝ,0≤ C ∧∀ j:J i, PairA (s i) (C*x i j^d) (θ i j) (P i j) (Q i j)

def Slate (x θ:(i:I)→ J i→ℝ)(P Q:(i:I)→ J i→ V) := ∃ d:ℕ,∀ i:I,∃ C:ℝ,0≤ C ∧ ∀ j,twain (C*x i j^d) (θ i j) (P i j) (Q i j)
variable {β:I→Type*} {P Q F H:(i:I)→ J i→ Ten V (Cloth (α i)) r}
lemma Satin.start (h:∀ i j,PairA (s i) (x i j) (θ i j) (P i j) (Q i j)): Satin x θ s P Q:=⟨1,fun i=>⟨1,zero_le_one,fun j=>by rw [one_mul,pow_one]; exact h i j⟩⟩
lemma Satin.fixed (h:∀ i,Brite (x i) (θ i)){P:(i:I)→ Ten V (Cloth (α i)) r}(e:∀ i, ∃ C:ℝ,Amber terrain (s i) C (P i)): Satin x θ s (fun i _=> P i) (fun i _=> P i) := by
   refine ⟨0,fun i=> ?_⟩; obtain ⟨a,ha⟩:= e i; exact ⟨a,ha.1,fun j=> by rw [pow_zero,mul_one]; exact PairA.echo ha ((h i).dist j)⟩
lemma Satin.add (h:Satin x θ s P Q)(g:Satin x θ s F H)(b:∀ i,Brite (x i) (θ i)): Satin x θ s (P+F) (Q+H) := by
   obtain ⟨d,f⟩:=h; obtain ⟨e,g⟩:=g; refine ⟨d+e, fun i=> ?_⟩
   obtain ⟨a,ha,h⟩:=f i; obtain ⟨A,hA,H⟩:=g i
   exact ⟨a+A,add_nonneg ha hA,fun j=> (((h j).add (H j)).up (roof_pair _ _ _ ((b i).large _) ha hA d e) ((b i).dist _))⟩
lemma Satin.neg (h:Satin x θ s P Q): Satin x θ s (-P) (-Q):= by obtain ⟨d,H⟩:=h; refine ⟨d,fun i=>?_⟩; obtain ⟨a,h,e⟩:=H i; exact ⟨a,h,fun j=> (e j).neg⟩
lemma Satin.sub (h:Satin x θ s P Q)(g:Satin x θ s F H)(b:∀ i,Brite (x i) (θ i)): Satin x θ s (P-F) (Q-H):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add g.neg b
lemma Satin.zero : Satin x θ s (0:(i:I)→ J i→ Ten V (Cloth (α i)) r) 0:=⟨0,fun i=>⟨0,le_rfl, fun j=> by rw [zero_mul]; exact PairA.zero⟩⟩
lemma Satin.spare {P Q:(i:I)→ J i→ Ten V (Cloth (α i ⊕ β i)) r}(h:Satin x θ s P Q): Satin x θ s (fun i j=> scoop (P i j)) (fun i j=> scoop (Q i j)) := by
    obtain ⟨d,h⟩:=h; refine ⟨d,fun i=>?_⟩; obtain ⟨a,p,H⟩:=h i; exact ⟨a,p, fun j=> (H j).spare⟩
lemma Satin.sum (h:∀ i,Brite (x i) (θ i)){S:Finset U}{P Q:U→(i:I)→ J i→ Ten V (Cloth (α i)) r} (he:∀ i∈S,Satin x θ s (P i) (Q i)): Satin x θ s (fun i j=>∑ b∈S,P b i j) (fun i j=>∑ b∈S,Q b i j) := by
  classical
  induction S using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Satin.zero
  | @insert i S p ih=> simp_rw [Finset.sum_insert p]; exact (he i (Finset.mem_insert_self ..)).add (ih fun j hj=> he j (Finset.mem_insert_of_mem hj)) h
variable [NormedSpace ℝ V]
omit [NormedSpace ℝ V] in
lemma Slate.one {P:I→V}(h:∀ i,Brite (x i) (θ i)): Slate x θ (fun i _=>P i) (fun i _=>P i):= ⟨0,fun i=>⟨‖P i‖,norm_nonneg _,fun j=>by rw [pow_zero,mul_one]; exact twain.one _ _ ((h i).dist _) le_rfl⟩⟩
lemma Satin.μ {u v:(i:I)→ J i→ℝ}(p:Slate x θ u v)(h:Satin x θ s P Q): Satin x θ s (fun i j=> u i j • P i j) (fun i j=> v i j • Q i j):=by
   obtain ⟨d,E⟩:=h; obtain ⟨e,p⟩:=p; refine ⟨d+e, fun i=> ?_⟩
   obtain ⟨a,ha,h⟩:= E i; obtain ⟨A,hA,H⟩:=p i; refine ⟨2*a*A,by positivity,fun j=>?_⟩
   rw [pow_add, show 2*a*A*(_*_)= 2*(a*x i j^d)*(A*x i j^e) by ring]; exact (h j).μ (H j)
lemma Satin.tiles {P Q:(i:I)→ J i→ Gen V (Cloth (α i))}(h:Satin x θ t (fun i j=> P i j r) (fun i j=> Q i j r))(L:I→Side)(he:∀ i,0≤s i)(HP:∀ i,s i/(L i).val ≤ t i): Satin x θ s (fun i j=>plants (L i) (P i j) r) (fun i j=>plants (L i) (Q i j) r) := by
   obtain ⟨d,p⟩:=h; refine ⟨d,fun i=>?_⟩; obtain ⟨a,h,e⟩:=p i
   refine ⟨Fintype.card (Site (L i))*a*Real.exp (8*s i), by positivity,fun j=> ?_⟩
   have hf:= (e j).pack (he i) (HP i); convert! hf using 1; ring
omit [NormedSpace ℝ V] in
lemma Satin.haul {P Q:(i:I)→ J i→ Ten ℝ (YForest G) 2}(h:Satin x θ s P Q)(p:∀ i,0<s i): Slate x θ (fun i j=> readSun (P i j)) (fun i j=> readSun (Q i j)):=by
   obtain ⟨d,H⟩:=h; refine ⟨d,fun i=>?_⟩; obtain ⟨a,h,e⟩:= H i
   let D:=ceilPoly 2 (s i/2)*sheetPay (s i/2); have he:0≤D:= mul_nonneg (ceilPoly_pos 2 (s i/2)).le (sheetPay_pos _ (by linarith [p i])).le
   refine ⟨a*D,mul_nonneg h he,fun j=>?_⟩
   have ht:= sun_cost (e j).pose (p i); have hh:= sun_cost (e j).vale (p i); have hf:= sun_cost (e j).visit (p i)
   refine ⟨ht.trans_eq (by unfold D; ring),hh.trans_eq (by unfold D; ring),?_⟩
   rw [← sun_sub (e j).pose (e j).vale (p i) (p i)]; exact hf.trans_eq (by unfold D; ring)
variable [∀ i,Fintype (α i)][CompleteSpace V]
variable {B:I→ℝ}
lemma Satin.meld {P Q:(i:I)→ J i→ Gen V (Cloth (α i))}{M N:(i:I)→ J i→ ropes Cover (α i) (β i)}(e:∀ i,0≤t i)(he:∀ i,t i<s i)(b:∀ i,0≤B i)(h:∀ i,Brite (x i) (θ i))(g:∀ i j,Ballast (s i) (B i) (θ i j) (M i j) (N i j))(p:Satin x θ s (fun i j=> P i j r) (fun i j=> Q i j r)): Satin x θ t (fun i j=>prism (M i j) (P i j) r) (fun i j=>prism (N i j) (Q i j) r) := by
   obtain ⟨d,p⟩:=p; refine ⟨d,fun i=>?_⟩; obtain ⟨A,hp,H⟩:=p i
   refine ⟨(r+1:ℕ)*(B i)^r*A*tieN (α i) (s i-t i) r,?_ ,fun j=>?_⟩
   · have hg:=b i; have ht:=tieN_nn (α:=α i) (sub_pos.mpr (he i)) r; positivity
   have hv:= PairA.prune_bill (g i j) ((h i).dist _) (he i) (e i) (H j)
   convert! hv using 1; ring
end furl
end YM.WilsonCoeffUV.Bank
