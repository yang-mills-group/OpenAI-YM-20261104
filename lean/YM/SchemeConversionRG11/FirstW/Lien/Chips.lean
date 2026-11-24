import YM.SchemeConversionRG11.FirstW.Lien.Fair
/-! Quadratic derivatives indeed do the pricing of arbitrary legitimate hats (operators). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {i j k : ℕ} {I : Type*} [Fintype I]
abbrev identifies (I : Type*) (k : ℕ) (p : Cache I) := IsWeightedHomogeneous (fun _=>(1:ℕ)) p k
omit [Fintype I] in
lemma derivative_part (p:Cache I) (hp:identifies I (k+1) p) (i:I) : identifies I k (D1 i p) := by
  intro t h
  have hh:= hp (mem_support_iff.mp (leafup p i (mem_support_iff.mpr h))); simp only [map_add,Finsupp.weight_single,one_smul] at hh; omega
omit [Fintype I] in
lemma entry_zero (p:Cache I) (hp:identifies I (k+1) p) : coeff 0 p=0 := by by_contra h; have ht:=hp h; rw [map_zero] at ht; omega
omit [Fintype I] in
lemma dd_const (p:Cache I) (hp:identifies I 0 p) : p=C (coeff 0 p) := by
 refine MvPolynomial.ext _ _ (fun s=>?_); by_cases h:s=0; · simp [h]
 rw [coeff_C_of_ne_zero h]; by_contra he
 obtain ⟨i,hi⟩:= Finsupp.ne_iff.mp h
 change s i≠0 at hi
 have hh := Finsupp.le_weight (fun _=> (1:ℕ)) (s:=i) one_ne_zero s
 rw [hp he] at hh; omega
set_option maxHeartbeats 500000 in
lemma cash_quad (p:Cache I) (hp:identifies I 2 p): p = ∑ i:I,∑ j:I,C ((1/2:ℂ)*loot p i j)*(X i* X j) := by
  have he i j : D1 j (D1 i p)= C (loot p i j):= dd_const _ (derivative_part _ (derivative_part p (k:=1) hp i) j)
  let D(i:I) := ∑ j:I,C (loot p i j) * X j
  have hd (i:I): D1 i p = D i := by
    apply const_right
    · rw [entry_zero (D1 i p) (derivative_part p hp i)]; simp [D,coeff_sum]
    intro j; rw [he]; unfold D; simp only [D1,map_sum,pderiv_C_mul];rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)];simp; intro l _ hl; rw [pderiv_X_of_ne hl,mul_zero]
  let P:I→I→Cache I := fun i j=> C ((1/2:ℂ)*loot p i j)*(X i* X j)
  apply const_right
  · rw [entry_zero _ hp,coeff_sum]; symm; apply Finset.sum_eq_zero; intro i _; rw [coeff_sum]; apply Finset.sum_eq_zero; intro j _; simp only [coeff_C_mul,X,monomial_mul]; simp -- s=0 support
  intro r; rw [hd r]; simp only [D1,map_sum,pderiv_C_mul]; simp only [pderiv_mul,mul_add]; -- want diagonal summing
  let a : I→I→Cache I := fun i j=> C ((1/2:ℂ)*loot p i j)*(pderiv r (X i)* X j)
  let b : I→I→Cache I := fun i j=> C ((1/2:ℂ)*loot p i j)*(X i *pderiv r (X j))
  have ha (i j:I): b i j=a j i := by unfold a b; rw [loot,commute]; unfold D1; unfold loot; rw [mul_comm (X i : Cache I)]
  change _=∑ i:I,∑ j:I,(a i j+b i j)
  simp_rw [ha,Finset.sum_add_distrib]; rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun i j=>a j i)] -- labels?
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ r)]; rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; unfold a; rw [pderiv_X_self,one_mul, ← add_mul,← map_add,show _+_ = loot p r j from by ring]
  intro j _ hj; unfold a; simp_rw [pderiv_X_of_ne hj,zero_mul,mul_zero,Finset.sum_const_zero]
lemma coin_caps (p : Part G 6) (h:uncap p∈ Reel G): identifies _ 2 p := by
  let k := fun x: Who G 6=> x.val
  have ht:= (vaulted.mp h).2.1
  intro s hs
  have hp : coeff (Finsupp.mapDomain k s) (uncap p)≠0 := by rwa [uncap,coeff_rename_mapDomain k Subtype.val_injective]
  have hh(s : Who G 6→₀ℕ) : Finsupp.weight (fun _=> (1:ℕ)) s= Finsupp.weight (fun _=>(1:ℕ)) (Finsupp.mapDomain k s) := by
    induction s using Finsupp.induction_linear with | zero=> simp | add a b i j=>simp [map_add,Finsupp.mapDomain_add,←i,←j] | single a b=> simp only [Finsupp.weight_single,Finsupp.mapDomain_single]
  exact (hh s).trans (ht hp)
def ballot {U : Type*} [AddCommGroup U] [Module ℝ U] (K : U→ₗ[ℝ] (I→ℝ)) (p : Cache I): U→ₗ[ℝ] U→ₗ[ℝ]ℂ:=
  ∑ i:I,∑ j:I,((1/2:ℂ)*loot p i j) • ((((LinearMap.mul ℝ ℝ).compl₂ (LinearMap.proj j ∘ₗ K)).comp (LinearMap.proj i ∘ₗ K)).compr₂ Complex.ofRealCLM.toLinearMap)
lemma ball_val {U : Type*} [AddCommGroup U] [Module ℝ U] (K:U→ₗ[ℝ] (I→ℝ))(p:Cache I) (X Y:U) : ballot K p X Y= ∑ i:I,∑ j:I, ((1/2:ℂ)*loot p i j) * (↑(K X i*K Y j):ℂ):=by simp only [ballot,LinearMap.sum_apply];rfl
lemma ball_sym {U : Type*} [AddCommGroup U] [Module ℝ U] (K:U→ₗ[ℝ] (I→ℝ)) (p:Cache I) (X Y:U) : ballot K p X Y=ballot K p Y X := by rw [ball_val,ball_val,Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; unfold loot; rw [commute,mul_comm (K X b)]
lemma held (p : Part G 6) (hp:uncap p∈ Reel G) (A: Field4 G): sun A (uncap p)= ballot (taxes 6 0 1) p A A:= by
  rw [sun,←salute_read,ball_val]
  have he : salute 6 (stageW G A)=taxes 6 0 1 A:=rfl
  rw [he]; nth_rw 1 [cash_quad p (coin_caps p hp)]; simp only [map_sum,map_mul,look, aeval_C, aeval_X, Complex.ofReal_mul,RingHom.id_apply,Algebra.algebraMap_self]
lemma ballots (p:Part G 6) (hp:uncap p∈ Reel G) (A B:Field4 G): chord A B (uncap p)= ballot (taxes 6 0 1) p A B := by
  rw [chord_at]; simp_rw [held p hp,map_add,LinearMap.add_apply]; rw [ball_sym (p:=p) (X:=B) (Y:=A)]; ring
-- noninvariant quadratics still descend. uncap require constructor from within labels (invariance not necessary)
lemma songs (p:Labels.Pol G) (hp:p∈Labels.limited G k) : ∃ u:Part G k,uncap u=p := by
 apply exists_rename_eq_of_vars_subset_range p (fun x:Who G k=>x.val) Subtype.val_injective
 intro i hi
 obtain ⟨b,hb,hi⟩:= (mem_vars_iff_mem_support ..).1 hi
 have hh:Labels.height b≤k:= (mem_restrictSupport_iff ℂ).1 hp hb
 exact ⟨⟨i, le_trans (Nat.le_add_right i.1 2) ((Finsupp.le_weight_of_ne_zero' Labels.generation (Finsupp.mem_support_iff.mp hi)).trans hh)⟩,rfl⟩
lemma bills (p : Reel G) : ∃ L:Field4 G →ₗ[ℝ] Field4 G →ₗ[ℝ] ℂ,∀ A B, L A B=chord A B p.val := by
 obtain ⟨u,h⟩:= songs _ (vaulted.mp p.property).1
 exact ⟨_,fun A B=> by rw [← h]; exact (ballots u (h ▸ p.property) A B).symm⟩
lemma dead_note (A:Nu G j) (h:quietly A.val) (p:Reel G) (B:Field4 G): chord A.val B p.val=0 := by
 obtain ⟨u,hu⟩:=songs _ (vaulted.mp p.property).1; rw [←hu,ballots u (hu ▸ p.property),ball_val]; obtain ⟨s,_,hs,_⟩:= primitive A.val j (cabin_stor A.property) h
 rw [←hs]; simp [taxes,letter_T]
end YM.RG11.FirstW
