import YM.SchemeConversionRG11.FirstW.Ore.Bills
/-! Polynomial boats on covers and tensor tests. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{Q:Wash}{R:ℝ}
section wave
variable {A B:ℕ→Field4 G}{U : Type*} {a b : ℤ} {K : Set E4}
lemma deaf_plus (h:Deaf T K a A) (p:Deaf T K a B): Deaf T K a (fun i=> A i+B i):= by
 refine ⟨fun i=> (h.cap i).add (p.cap i),fun i j=>?_⟩; have ht(v:ℕ): field4 i (A v+B v)=field4 i (A v)+field4 i (B v):=rfl; simp_rw [ht, up]; simp only [Pi.add_apply, add_sub_add_comm]; exact (h.loft i j).add (p.loft i j)
lemma deaf_zero : Deaf T K a (fun _=> (0:Field4 G)) := by
 refine ⟨fun _=> Melody.zero,fun i j=>?_⟩; simp only [up,field4,Pi.zero_apply,sub_zero]; exact Melody.zero
lemma deaf_sum {f:U→ℕ→ Field4 G}(s:Finset U)(h:∀ i∈s,Deaf T K a (f i)): Deaf T K a (fun j=>∑ i∈s,f i j):=by
 induction s using Finset.induction with| empty=>simp only [Finset.sum_empty]; exact deaf_zero|insert x s hx ih=> simp only [Finset.sum_insert hx]; exact deaf_plus (h _ (Finset.mem_insert_self ..)) (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma melody_constH (g:ℕ→ℝ) (hf:Helen g) : Melody T K 0 (fun i _=>g i):=by
 obtain ⟨x,H⟩:=hf; refine ⟨fun _=> x,fun σ hs v hv p hp=>?_⟩; simp only [ped,zpow_zero,one_smul]; exact H.comp hs
lemma up_smul_f(x:ℝ)(i:Axis)(y:Cover→G.Color)(j:Cover): up i (fun v=>x • y v) j=x • up i y j:=by simp only [up,smul_sub]
lemma deaf_mul (h:Deaf T K a A)(g:ℕ→ℝ)(hf:Helen g) : Deaf T K a (fun i=>g i • A i):=by
 let L : ℝ→L[ℝ] G.Color→L[ℝ] G.Color:= (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ G.Color)
 have hp:= melody_constH (T:=T) (K:=K) g hf
 refine ⟨fun i=>?_,fun i j=>?_⟩
 · simpa only [zero_add,L,ContinuousLinearMap.smulRight_apply] using! hp.linked (h.cap i) L
 have hev(i:Axis)(k:ℕ): field4 i (g k • A k)=fun v=>g k• field4 i (A k) v:=rfl
 simp_rw [hev,up_smul_f]; simpa only [zero_add,L,ContinuousLinearMap.smulRight_apply] using! hp.linked (h.loft i j) L
lemma changes {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:ℕ → Cover→E} (g: Melody T K (a+b) f): Melody T K a (fun i x=> T.gap i ^ b • f i x) := by
 obtain ⟨v,g⟩:=g; refine ⟨v,fun σ hs x hx p hp=>?_⟩; exact (g σ hs x hx p hp).congr (fun i=>by dsimp only [ped]; rw [smul_smul, zpow_add₀ (T.positive _).ne'])
lemma changesDeaf (e : Deaf T K (a+b) A) : Deaf T K a (fun i=> T.gap i ^ b • A i):=by
 refine ⟨fun i=>changes (e.cap i),fun i j=>?_⟩; have he k: field4 i (T.gap k^b • A k) = fun v=> T.gap k ^ b • field4 i (A k) v:=rfl
 simp_rw [he,up_smul_f]; apply changes; rw [show a-1+b=a+b-1 by omega]; exact e.loft i j
lemma Colorish (U V:Type*) [AddCommGroup U][Module ℝ U] [FiniteDimensional ℝ U] [AddCommGroup V] [Module ℝ V] (a:ℕ→U) (L: ℕ→ U→ₗ[ℝ] V): ∃ (I:ℕ)(f:Fin I→ (U→ₗ[ℝ]ℝ))(b:Fin I→ U),∀ i,L i (a i) = ∑ j:Fin I, f j (a i) • L i (b j) := by
 let b:= Module.finBasis ℝ U
 refine ⟨_,b.coord,b,fun i=>?_⟩
 nth_rw 1 [← b.sum_repr (a i)]; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; exact (L i).map_smul ..
lemma boating (j:ℕ)(p:ℕ→ Nu G j)(hp:Book p): Deaf T K (j:ℤ) (fun i=>(p i).val) := by
 obtain ⟨I,f,b,H⟩:= Colorish (Nu G j) (Field4 G) p (fun _=>(cabin G j).subtype)
 have he (i:ℕ) : (p i).val=∑ s:Fin I,f s (p i) • (b s).val := H i
 simp_rw [he]; apply deaf_sum; intro i _; exact deaf_mul (knownP j _ (b i).property K) _ (hp (f i))
lemma arms (p:Age G)(hp:∀ i≤4, Book (p i)): Deaf T K (-1) (composeR T 4 p):=by
 unfold composeR; apply deaf_sum; intro i hi
 simp_rw [←zpow_natCast, Nat.cast_add,Nat.cast_one]; apply changesDeaf (a:=-1); rw [show (-1:ℤ)+((i:ℤ)+1)=i by omega]
 exact boating i _ (hp _ (Finset.mem_range_succ_iff.mp hi))
end wave
variable {q m:ℕ}
def stampB (F:Labels.Frames G) (B:ℕ→Pack F) (T:Itinerary)(Q:Wash):= paidC T 5 (fun i=> bondM F T i Q - glyph F (B i)) ∧ Level (fun i=> T.gap i • B i)
lemma adaptive {U V:Type*} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] [AddCommGroup V] [Module ℝ V][FiniteDimensional ℝ V] (f:ℕ→U→ₗ[ℝ]V→ₗ[ℝ]ℂ)(p:ℕ→U)(q:ℕ→V)(h:∀ x y,Helen (fun i=> f i x y))(hp:Book p)(hq:Book q): Helen (fun i=>f i (p i) (q i)):=by
 obtain ⟨j,C,g,H⟩:= Colorish U U p fun _=>LinearMap.id
 obtain ⟨k,D,b,Hb⟩:= Colorish V V q fun _=>LinearMap.id
 simp only [LinearMap.id_coe,id_eq] at H Hb
 -- don't simp loops inside p-coeff
 let L (i:ℕ) := (∑ v:Fin k, ∑ w:Fin j, D v (q i) • (C w (p i) • f i (g w) (b v)))
 have he(i:ℕ): f i (p i) (q i)= L i:=by nth_rw 1 [H i,Hb i]; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum];rfl
 simp_rw [he,L]; apply collectH; intro s _; apply collectH; intro t _; obtain ⟨x,hx⟩:=hp (C t); obtain ⟨y,hy⟩:=hq (D s); obtain ⟨z,hz⟩:= h (g t) (b s); exact ⟨_, hy.smul (hx.smul hz)⟩
lemma candles (hc:MarkGrid T c)(p:Age G)(r:Age G)(hp:∀ i≤4,Book (p i))(hr:∀ i≤4,Book (r i)) (B:ℕ→Pack F) (h:stampB F B T Q)(a:E F 6) :
 Helen (fun i=> (T.gap i)^(-6:ℤ) • bleach T Q (B i) i a (composeR T 4 p i) (composeR T 4 r i)) := by
 have he (v w:ℕ)(hv:v≤4)(hw:w≤4): Helen (fun i=> T.gap i^((v:ℤ)+w-4) • bleach T Q (B i) i a (p v i).val (r w i).val) := by
   let f(i:ℕ):Nu G v →ₗ[ℝ] Nu G w →ₗ[ℝ]ℂ:= T.gap i^((v:ℤ)+w-4) • (((bleach T Q (B i) i a).comp (cabin G v).subtype).compl₂ (cabin G w).subtype)
   have hr0 (x:Nu G v) (y:Nu G w) : Helen (fun i=> f i x y):=by
      have hy:= scaled_ball hc Q h.1 h.2 a (boards v hv x) (boards w hw y) v w (by rw [boards_val]; exact x.property) (by rw [boards_val]; exact y.property)
      simp only [f,LinearMap.comp_apply,LinearMap.compl₂_apply,LinearMap.smul_apply]; simp only [boards_val] at hy; exact hy
   have hy:= @adaptive (Nu G v) (Nu G w) _ _ _ _ _ _ f (p v) (r w) hr0 (hp v hv) (hr w hw)
   simp only [f,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.compl₂_apply,Submodule.subtype_apply] at hy; exact hy
 simp only [composeR,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.smul_sum]; apply collectH; intro u hu; apply collectH; intro v hv; simp only [smul_smul]
 obtain ⟨x,hx⟩:= he v u (Finset.mem_range_succ_iff.mp hv) (Finset.mem_range_succ_iff.mp hu)
 exact ⟨x,hx.congr fun i=>by congr 1; simp_rw [←zpow_natCast,←zpow_add₀ (T.positive i).ne']; congr 1; omega⟩
end YM.RG11.FirstW
