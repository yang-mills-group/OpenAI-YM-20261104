import YM.XSpace.SpanVoice
/-!
# Extension from disjoint aux pairs to **all** pairs
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal
open scoped BigOperators Topology Classical
variable {G : Gauge} (C₀:G.ColorIndex) {S:Finset E4} {L A : Finset (World G)} {h : ℕ} {P Q:Pol G}
local notation "V" => Module.Dual ℝ (Supply S h)
lemma backs_add (U W: V) (i : G.ColorIndex): backed (G:=G) (U+W) i= backed U i + backed W i:=by funext x; by_cases hi : x.2.2=i <;> simp [backed,hi]
lemma backs_smul (U: V) (t :ℝ) (i:G.ColorIndex): backed (G:=G) (t • U) i= (t:ℂ) • backed U i:=by funext x; by_cases hi:x.2.2=i <;> simp [backed,hi]
lemma plow_first (P:Pol G) (U W:V) (B:Lane G) : plow (backed (U+W)) B P= plow (backed U) B P+plow (backed W) B P:=by simp_rw [plows,backs_add,slit_linear,Finset.sum_add_distrib]
lemma plow_scale (P:Pol G) (a:ℝ) (U:V) (B:Lane G) : plow (backed (a • U)) B P=(a:ℂ) • plow (backed U) B P:=by simp_rw [plows,backs_smul,slit_smul,Finset.smul_sum]

def quotePair (S:Finset E4) (h:ℕ) (P Q:Pol G) (B:Lane G): Module.Dual ℝ (Supply S h) →ₗ[ℝ] ℂ where
  toFun k := permit S Q (plow (backed k) B P)
  map_add' x y:=by rw [plow_first,map_add]
  map_smul' x y:=by rw [plow_scale,map_smul,Complex.real_smul]; rfl
lemma quote_val (Q:Pol G) (U:V) (B:Lane G): quotePair S h P Q B U=permit S Q (plow (backed U) B P):=rfl
lemma spoken_plow (hP:P∈Lap.scope A) (HA:Good S h A) (x:Ph) (he:x.1∉S) (B:Lane G):
    plow (backed (voice S h C₀ x)) B P=plow (fast S x) B P:=by
  rw [plows,plows]; refine Finset.sum_congr rfl fun i _=> (split_eq _ _ (fun a ha=>bow C₀ h _ _ i he (HA a ha)) (split_in _ _ hP)).symm
include C₀ in
lemma every_plow (hP:P∈Rain S A) (HA:Good S h A) (U W:V): plow (backed U) (backed W) P∈Rain S A:=by
  have H := (rain_iff.mp hP).1
  refine rain_iff.mpr ⟨plow_fit _ _ H,fun L Q hQ=>?_⟩
  let T:= S∪ L.image Prod.fst
  suffices ht : quotePair S h P Q (backed W)=0 by exact (quote_val _ U _).symm.trans (DFunLike.congr_fun ht U)
  refine LinearMap.ext_on (ranged C₀ S T h Finset.subset_union_left) ?_; rintro u ⟨x,hx,rfl⟩; let B:= fast (G:=G) S x
  change _=0; rw [quote_val,spoken_plow C₀ H HA x (fun hw=> hx (Finset.mem_union_left _ hw)),plow_swap]
  change quotePair S h P Q B W=0
  suffices ht: quotePair S h P Q B=0 by rw [ht,LinearMap.zero_apply]
  refine LinearMap.ext_on (ranged C₀ S (insert x.1 T) h (Finset.subset_union_left.trans (Finset.subset_insert ..))) ?_
  rintro w ⟨y,hy,rfl⟩; have ht : y.1 ≠ x.1 ∧ y.1∉T:=by simpa using hy
  rw [quote_val,spoken_plow C₀ H HA _ (fun he=> ht.2 (Finset.mem_union_left _ he))]; exact rain_plow C₀ hP hQ y x ht.2 hx ht.1
end YM.XSpace.Legs
