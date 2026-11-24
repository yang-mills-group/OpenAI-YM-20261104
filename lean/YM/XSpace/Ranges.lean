import YM.XSpace.Pointer
/-!
# Homogeneous column operations through slot degree
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Pages
open Function Set Filter Lattice Chart2 Lows Mu Finsupp MvPolynomial Contraction Next.Rank.Normal Stall
open scoped Topology ContDiff BigOperators Classical
variable {I J F:Type*}{m n:ℕ}{G:Gauge}
abbrev solo (I:Type*) : I→ℕ:= fun _=>1
abbrev Volume (s:I→₀ℕ):=weight (solo I) s
abbrev Hom (p:poly I)(n:ℕ):= IsWeightedHomogeneous (solo I) p n
abbrev rank (n:ℕ)(I:Type*) := weightedHomogeneousSubmodule ℂ (solo I) n
abbrev strike (I:Type*)(n:ℕ):= Cut (solo I) n
lemma home_m (s:I→₀ℕ)(c:ℂ): Hom (monomial s c) (Volume s):= isWeightedHomogeneous_monomial _ _ _ rfl
lemma size_nil {s : I→₀ℕ} (h: Volume s=0): s=0:= by
  ext1 i; by_contra ha
  have hv:= Finsupp.mem_support_iff.mpr (show s i ≠ 0 from ha); change s.sum (fun _ y=> y • (1:ℕ))=0 at h; unfold Finsupp.sum at h; have he:= (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>Nat.zero_le (_:ℕ))).1 h i hv; simp at he; exact ha he
lemma shroud {p:poly I}(h:p∈DegZ I 0): ∃ z,p=C z:=by
  use ∑ i∈p.support,coeff i p; conv_lhs=> rw [p.as_sum]; skip
  rw [_root_.map_sum]; exact Finset.sum_congr rfl fun i hi=>(by rw [size_nil (Nat.eq_zero_of_le_zero ((bounded _).1 h _ hi))]; rfl)
lemma hom_g {p:poly I}(h:p∈rank n I): p∈DegZ I n:= Lows.gated _ _ h
def dilate (I:Type*)(z:ℂ): poly I→ₐ[ℂ] poly I:= aeval fun i=> z • X i
lemma volume_fee (s:I→₀ℕ)(i:I):Volume (s+single i 1)=Volume s+1:= by unfold Volume; rw [map_add,weight_single,one_smul]
lemma dilate_one (z:ℂ)(s:I→₀ℕ)(k:ℂ): dilate I z (monomial s k)= z^(Volume s) • monomial s k:= by
  apply Extra.FD.per_factor s; simp [dilate]
  intro q i h; rw [volume_fee q i, monomial_add_single,pow_one,map_mul,h,dilate,aeval_X, smul_mul_smul, pow_add];simp
lemma dil_co (i:I→₀ℕ)(p:poly I)(z:ℂ): coeff i (dilate I z p)= z^ Volume i * coeff i p:=by
  rw [p.as_sum,_root_.map_sum,MvPolynomial.coeff_sum,MvPolynomial.coeff_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [dilate_one,coeff_smul]; by_cases h:j=i <;> simp [h]
lemma grows {p:poly I}(h:Hom p n) (z:ℂ): dilate I z p=z^n • p:=by ext i; rw [dil_co,coeff_smul]; by_cases hh:Finsupp.weight (solo I) i=n; simp [hh]; simp [h.coeff_eq_zero i hh]
lemma charge (P:Stamp G)(z:ℝ)(A:Trace.Contact G): pit (z • A) P=pit A (dilate _ z P):=by
  induction P using MvPolynomial.induction_on with
  | C a=> simp [dilate]
  | add x y h p=>simp only [map_add,h,p]
  | mul_X x i h=> rw [map_mul,map_mul,map_mul,h]; unfold dilate; rw [aeval_X,map_smul]; simp only [smul_eq_mul];simp [pit,numbers]
lemma glow {p:Stamp G}(h: ∀ (z:ℝ)(A:Trace.Contact G), pit (z • A) p=(z:ℂ)^n • pit A p): Hom p n:=by
  have hp(z:ℝ):dilate _ z p=(z:ℂ)^n • p:=same (fun A=>by rw [← charge,h,map_smul]); intro i hi; have hh:= congr_arg (coeff i) (hp 2); rw [dil_co,coeff_smul,smul_eq_mul,Complex.ofReal_ofNat] at hh; have he : (2:ℝ)^(Volume i)=2^n:=by exact_mod_cast (mul_right_cancel₀ hi hh)
  exact (pow_right_inj₀ (show 0<(2:ℝ) from by norm_num) (show (2:ℝ) ≠ 1 by norm_num)).1 he
lemma sags {p:Stamp G}(h:Hom p n)(z:ℝ)(A:Trace.Contact G): pit (z • A) p=(z:ℂ)^n*pit A p:=by rw [charge,grows h,map_smul]; rfl

private lemma stint (L:I→ℂ)(s:I→₀ℕ)(k:ℂ): slit L (monomial s k)∈rank (Volume s-1) I:=by
  apply Extra.FD.per_factor s; rw [show monomial (σ:=I) 0 k=C k from rfl,slit_C]; exact Submodule.zero_mem (rank (Volume (0:I→₀ℕ)-1) I) -- need slit
  intro p i h; rw [monomial_add_single,pow_one,mul_comm,slit_prod,C_mul',volume_fee p i]; simp only [Nat.add_sub_cancel]; refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (home_m p k))
  rcases Nat.eq_zero_or_pos (Volume p) with h|h1
  · rw [size_nil h,show monomial (σ:=I) 0 k=C k from rfl,slit_C,mul_zero]; exact Submodule.zero_mem _
  have he : 1+(Volume p-1)=Volume p:=by omega
  exact he ▸ (show X i * slit L (monomial p k)∈rank (1+(Volume p-1)) I from (isWeightedHomogeneous_X (R:=ℂ) (solo I) i).mul h)
lemma slanted {p:poly I}(h:p∈ DegZ I (n+1))(L:I→ℂ) : slit L p ∈ DegZ I n:=by rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ fun i hi=>higher (solo I) (?_) (hom_g (stint L i (coeff i p))); have he : Volume i≤n+1:= (bounded _).1 h _ hi; omega
lemma slit_degree {p:poly I}(h:Hom p (n+1))(L:I→ℂ): Hom (slit L p) n:=by
  rw [p.as_sum,map_sum]; apply IsWeightedHomogeneous.sum; intro i hi; have ht:= h (MvPolynomial.mem_support_iff.mp hi); have he : Volume i-1=n:=by rw [show Volume i=n+1 from ht]; omega
  exact he ▸ stint L i _
lemma ward_limit (Q:Symmetric I)(p:poly I) (h:p∈DegZ I (n+1)): milk Q p-p ∈ DegZ I n:=by
  have he (s:I→₀ℕ)(t:ℂ): milk Q (monomial s t)-monomial s t∈ DegZ I (Volume s-1):=by
    classical apply Extra.FD.per_factor s; simp
    intro v i h; rw [monomial_add_single,pow_one,mul_comm,feeds, add_sub_right_comm, ← mul_sub,volume_fee v i]; simp only [Nat.add_sub_cancel]; refine Submodule.add_mem _ ?_ (slit_bound _ _ (wick_bound _ _ (has_self _ _ t)))
    rcases Nat.eq_zero_or_pos (Volume v) with h|h0; · simp [size_nil h]
    exact (show 1+(Volume v-1)=Volume v by omega) ▸ bounds_mul (solo I) (show X i ∈ DegZ I 1 from hom_g (isWeightedHomogeneous_X ..)) h
  rw [p.as_sum,map_sum, ← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i hi; apply higher _ _ (he ..); have ht:Volume i≤ n+1:=(bounded _).1 h _ hi; omega
-- reconstruct through unit cost grade
lemma known {p:poly I}(h:p∈ DegZ I n): p=∑ i∈Finset.range (n+1), strike I i p:=by have ht:=trunc_eq (solo I) h; rw [trunc,LinearMap.sum_apply] at ht; exact ht.symm
lemma strand {p:poly I}(h:Hom p n)(he : n ≠ 0): aeval (0:I→ℂ) p=0:=by
  have hx: constantCoeff p=0:=by rw [constantCoeff_eq]; exact h.coeff_eq_zero _ (by simp [Ne.symm he])
  simp [hx]
end YM.XSpace.Pages
