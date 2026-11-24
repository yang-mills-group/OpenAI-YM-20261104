import YM.XSpace.Symphony
/-! # Arrays at requested placements through formal positions

Before expressing in their determined coupling. Prepare literal source-coefficient
vertex evaluation as needed (use even quotient beam at each site). Reading of correlations ALWAYS
multiplies engineering then computes vacuum normalization. Service law for smeared profile.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter PowerSeries Trace Graph3 Photo Cirrus Normalize Tornado Retirement Structure1 AxesTangent Lattice
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:ℕ} (W:Initialize G)(V:Normalize.Store G)(d:ℕ)(x:Sample n)(p:Tags G d n)
def regal (i:x.F.Sites): Sec G d→ₗ[ℂ] Bare.Series (W.tree (grab x).p) G:= ∑ k: Fin (d+1), W.atSite x.F k.val i ∘ₗ Normalize.part d k.val
lemma regals {j:ℕ}(T:HP G j)(h:j≤d)(i:x.F.Sites): regal W d x i (en h T)= W.atSite x.F j i T:=by unfold regal; rw [LinearMap.sum_apply,Finset.sum_eq_single ⟨j,Nat.lt_add_one_iff.mpr h⟩]; rw [LinearMap.comp_apply,part_same]; intro b _ hb; rw [LinearMap.comp_apply, part_other _ (mt Fin.ext hb),map_zero]; simp
lemma oak (i:x.F.Sites): regal W d x i (leaf G d)=1:=by
  let T:HP G 0:=⟨1,(leaf G 0).property,MvPolynomial.isWeightedHomogeneous_one ..⟩; rw [show leaf G d=en (Nat.zero_le d) T from rfl,regals,Initialize.atSite,LinearMap.smul_apply,pow_zero,inv_one,one_smul,On.stencil_unit (he:=rfl)] -- parser
-- validation (no silent dimensional projection on point kernels)
def numberA (S:Finset (Fin n)): PowerSeries ℂ:= Bare.normalized _ G (∏ i∈ S,regal W d x ((chartV x) i) (p i))
lemma lit_up (e:ℕ): live W d x e p= coeff e (numberA W d x p Finset.univ):=by
  let A := Bare.Series (W.tree x.F.p) G; let M := MultilinearMap.mkPiAlgebra ℂ (Fin n) A
  let P : Point G d n := ((coeff (R:=ℂ) e) ∘ₗ Bare.normalized (W.tree x.F.p) G).compMultilinearMap (M.compLinearMap (fun i=>regal W d x (chartV x i))); change _= P p; apply congr_arg (fun x:Point G d n=>x p); apply whom; intro j q h; rw [lives W d x _ h]; unfold P; rw [Initialize.atTuple_eq]; change _= coeff e (Bare.normalized _ G (∏ i,regal W d x (chartV x i) _)); unfold shells; simp_rw [regals] -- check signature lower
-- realm point before moment test. Gauge determinant already included.
def cooked (e:ℕ) : Point G d n:=∑ u∈tally e n,(live W d x (u none)).compLinearMap (fun i=>coeff (u (some i)) (deck (V.layout W (grab x) d)))
lemma cooks (e:ℕ): cooked W V d x e p=∑ u∈tally e n, live W d x (u none) (pulseU u (deck (V.layout W (grab x) d)) p):=by simp only [cooked,sum_apply];rfl
lemma smeared (m:Mesh)(e:ℕ)(t:Test n): Deposit m (fun i=>cooked W V d i e p) t= V.opens W m d e n t p:=by rw [← V.fits_walk W m d,really]; simp_rw [← deposit_live W _ m _ t]; unfold Deposit; simp_rw [cooks,grab,Finset.mul_sum]; rw [Finset.sum_comm (t:=tally ..)]
-- subarray with only these sites in the measure (keep positions). Terms with orders
-- outside are zero; each term here is the actual product insertion on the subset.
variable {d}
local notation "W₀" => V.layout W (grab x) d
def missing (s:Finset (Fin n)): Tags G d n:= fun i=> if i∈s then p i else leaf G d
lemma prime_deck (x:Normalize.Pick G d)(e:ℕ): (coeff e (deck x)) (leaf G d)= if e=0 then leaf G d else 0:=by rw [decked,pulling]; split_ifs; exact solitary ..; exact (x e).property.1
lemma glossL (u:Days n): numberA W d x (pulseU u (deck W₀) p) ∅=1:=by unfold numberA; simp only [Finset.prod_empty,Bare.normalize_unit]
lemma detail (e:ℕ)(τ:Finset (Fin n)): cooked W V d x e (missing p τ) = ∑ f∈ tally e n, if ∀ i:Fin n,i∉τ→ f (some i)=0 then coeff (f none) (numberA W d x (pulseU f (deck (V.layout W (grab x) d)) p) τ) else 0 :=by
  rw [cooks]; apply Finset.sum_congr rfl; intro f hf; by_cases h:∀ i: Fin n,i∉τ→ f (some i)=0
  · rw [if_pos h,lit_up]; apply congr_arg; unfold numberA; apply congr_arg; rw [← Finset.prod_subset (f:=fun i=> regal W d x (chartV x i) (pulseU f (deck W₀) (missing p τ) i)) (Finset.subset_univ τ) ?_]; apply Finset.prod_congr rfl; intro i hi; simp [pulseU,missing,hi]; intro i hi hj; unfold pulseU missing; rw [if_neg hj, prime_deck,if_pos (h i hj),oak] -- notation macro V shadow
  rw [if_neg h]; push Not at h; obtain ⟨i,hi,H⟩:=h; exact MultilinearMap.map_coord_zero (live W d x _) (i:=i) (by simp only [pulseU,missing,hi,prime_deck,if_neg H,↓reduceIte])
end YM.XSpace.Rose
