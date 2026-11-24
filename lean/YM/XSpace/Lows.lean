import YM.XSpace.Corridor

/-!
# Regulator contact polynomial stops, weight on harmonic open backgrounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Lows
open Function Set Filter Tensor Scale Trace Chart2 Mu JetGauge MvPolynomial Contraction Next.Rank.Normal Finsupp Lattice
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {d k n:ℕ}
abbrev Hat (G:Gauge)(d:ℕ) := Organ d G.Color
abbrev Index (G:Gauge)(d:ℕ) := Σ i:Fin (d+1),Fin (Module.finrank ℝ (Tune i.val G.Color))
abbrev Cap (G:Gauge)(d:ℕ) := MvPolynomial (Index G d) ℂ
instance tuning (d:ℕ)(F:Type*) [NormedAddCommGroup F][NormedSpace ℝ F] : Module.Free ℝ (Tune d F):= Module.Free.of_divisionRing ℝ (Tune d F)
instance ball (G:Gauge)(d:ℕ): NormedSpace ℝ (Tune d G.Color):= by unfold Tune; infer_instance
def bank (G:Gauge)(d:ℕ): Module.Basis (Index G d) ℝ (Hat G d):= Pi.basis fun i: Fin (d+1)=> Module.finBasis ℝ (Tune i.val G.Color)
def view (B:Hat G d) : Cap G d →ₐ[ℂ] ℂ:= aeval fun i : Index G d=> (((bank G d).repr B i : ℝ): ℂ)
def coin (i:Index G d) := 1 + i.1.val
lemma coin_ne (i:Index G d): coin i ≠0:=by unfold coin; omega
lemma sameCap {p q:Cap G d}(he:∀ x:Hat G d, view x p=view x q):p=q:= by
  let b:=bank G d
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) (fun _=> infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose y hy using fun i=>hx i (Set.mem_univ i)
  rw [show x=fun i=> ((b.repr (b.equivFun.symm y) i:ℝ):ℂ) by
    funext i; change x i= ((b.equivFun (b.equivFun.symm y) i:ℝ):ℂ); rw [b.equivFun.apply_symm_apply]; exact (hy i).symm]
  exact he _
lemma currency (a:ℝ)(X:Hat G d)(i:Index G d): view (orchestra d a X) (MvPolynomial.X i)=(a:ℂ)^coin i*view X (MvPolynomial.X i):=by
  unfold view; rw [aeval_X,aeval_X]; simp only [bank,Pi.basis_repr, Scale.orchestra_at,map_smul,Finsupp.smul_apply,smul_eq_mul]; push_cast;rfl
lemma currency_cost (a:ℝ)(r: Index G d→₀ℕ)(b:ℂ)(X:Hat G d): view (orchestra d a X) (monomial r b)=(a:ℂ)^ (Finsupp.weight coin r)*view X (monomial r b):=by
  classical apply Extra.FD.per_factor r; simp [view]
  intro u i hi; rw [monomial_add_single,pow_one,map_mul, map_mul,hi,map_add,weight_single,pow_add,currency,one_smul]; ring
lemma pure_entry (a:ℝ)(X:Hat G d){p:Cap G d}(h:IsWeightedHomogeneous coin p k): view (orchestra d a X) p=(a:ℂ)^k*view X p:=by rw [p.as_sum,map_sum,map_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [currency_cost,h (MvPolynomial.mem_support_iff.mp hi)]
lemma walk_cont (p:Cap G d): Continuous fun X:Hat G d=> view X p:=by
  unfold view; induction p using MvPolynomial.induction_on with
  | C a=> simp only [aeval_C]; apply continuous_const
  | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
  | mul_X p i hp=>simp_rw [map_mul,aeval_X]; exact hp.mul (Complex.continuous_ofReal.comp (LinearMap.continuous_of_finiteDimensional (𝕜:=ℝ) (E:=Hat G d) (F':=ℝ) ((bank G d).coord i)))

-- charge gradings
variable {I V: Type*} (w:I→ℕ)
abbrev Load (G:Gauge)(d n:ℕ):= weightBound (fun i:Index G d=>coin i) n
instance (u v:ℕ): FiniteDimensional ℂ (Load G u v):= by
  letI := (finite_of_nat_weight_le (coin (d:=u) (G:=G)) coin_ne v).to_subtype; exact Module.Finite.of_basis (basisRestrictSupport ℂ {i : Index G u →₀ ℕ | Finsupp.weight coin i≤v})

def trunc (n:ℕ): Module.End ℂ (poly I):= ∑ i∈Finset.range (n+1), weightedHomogeneousComponent w i
abbrev Cut (k:ℕ) := weightedHomogeneousComponent (R:=ℂ) w k
lemma gated (m:ℕ){p:poly I}(h:IsWeightedHomogeneous w p m): p ∈ weightBound w m:= (bounded w).mpr (fun i hi=> Eq.le (h (MvPolynomial.mem_support_iff.mp hi)))
lemma loaded (p:poly I)(n:ℕ): Cut w n p∈weightBound w n:= gated w n (weightedHomogeneousComponent_mem ..)
lemma transported (p:poly I)(n:ℕ):trunc w n p ∈ weightBound w n:=by unfold trunc; rw [LinearMap.sum_apply]; exact Submodule.sum_mem _ fun i hi=> higher w (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (loaded ..)
lemma trunc_ap (p:poly I)(i:I→₀ℕ)(n:ℕ): coeff i (trunc w n p)= if Finsupp.weight w i≤n then coeff i p else 0:=by
  classical unfold trunc; rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]; simp_rw [coeff_weightedHomogeneousComponent]; by_cases h: Finsupp.weight w i ≤ n <;> simp [eq_comm,h]
lemma trunc_eq {p:poly I}(h:p∈weightBound w n): trunc w n p=p:=by apply MvPolynomial.ext; intro i; rw [trunc_ap]; split_ifs with H; rfl; exact (not_not.mp fun he=> H ((bounded w).1 h i (MvPolynomial.mem_support_iff.mpr (Ne.symm he))))
lemma low_value (a:ℝ)(p:Cap G d)(n:ℕ)(X:Hat G d): view (orchestra d a X) (trunc coin n p)= ∑ m∈Finset.range (n+1), (a:ℂ)^m*view X (Cut coin m p):=by
  unfold trunc; rw [LinearMap.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [pure_entry _ _ (weightedHomogeneousComponent_mem ..)]
lemma uncut {p:Cap G d}(a:ℝ)(X:Hat G d)(h:p∈ Load G d n): view (orchestra d a X) p=∑ i∈Finset.range (n+1), (a:ℂ)^i*view X (Cut coin i p):= by nth_rw 1 [← trunc_eq coin h]; exact low_value ..
lemma cap_known (p:poly I): ∃ n,p∈weightBound w n:=by classical exact ⟨p.support.sup (Finsupp.weight w), (bounded w).mpr (fun i hi=> Finset.le_sup hi)⟩

def scale (a:ℝ): Cap G d→ₐ[ℂ] Cap G d:= MvPolynomial.aeval fun i:Index G d=> C ((a:ℂ)^(coin i))*X i
lemma scaled (a:ℝ)(p:Cap G d)(X:Hat G d): view X (scale a p)=view (orchestra _ a X) p:=by
  suffices h: (view X).comp (scale a)=view (orchestra _ a X) from DFunLike.congr_fun h p; ext1 i; rw [AlgHom.comp_apply,scale,aeval_X,map_mul,currency]; simp [view]
lemma scalable (a:ℝ){p:Cap G d}(h:IsWeightedHomogeneous coin p n): scale a p=((a:ℂ)^n) • p:= sameCap fun x=> by rw [scaled,pure_entry a x h,map_smul];rfl
lemma scale_saves (a:ℝ)(p:Cap G d)(k:ℕ): Cut coin k (scale a p)=(a:ℂ)^k • Cut coin k p:=by
  obtain ⟨n,h⟩:= cap_known coin p; rw [← trunc_eq coin h]; unfold trunc; simp_rw [LinearMap.sum_apply,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; have he:= weightedHomogeneousComponent_isWeightedHomogeneous (w:=coin) (φ:=p) (n:=i); rw [scalable a he,map_smul]; by_cases h:k=i; rw [h]; rw [he.weightedHomogeneousComponent_ne k h]; simp
lemma capacity (a:ℝ){p:Cap G d}(h:p∈Load G d n):scale a p ∈ Load G d n:=by
  rw [← trunc_eq coin h]; unfold trunc; rw [LinearMap.sum_apply,map_sum]; refine Submodule.sum_mem _ fun i hi=> ?_; exact higher coin (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (scalable a (weightedHomogeneousComponent_mem coin p i) ▸ Submodule.smul_mem (weightBound coin i) ((a:ℂ)^i) (loaded coin p i))

-- real Wick symbol evaluation as polynomials in the Harmonic data
def Audio (p:Module.Dual ℝ (Hat G d)): Cap G d:= ∑ i: Index G d, C (↑(p (bank G d i)):ℂ)*X i
lemma audio_at (p:Module.Dual ℝ (Hat G d))(X:Hat G d): view X (Audio p)=(p X:ℂ):=by
  unfold Audio; rw [map_sum]; conv_rhs=> rw [← (bank G d).sum_repr X,map_sum,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _=> ?_; simp only [view,map_mul,aeval_C, Algebra.algebraMap_self,RingHom.id_apply,aeval_X,map_smul,smul_eq_mul,Complex.ofReal_mul]; ring
lemma auditory (p:Module.Dual ℝ (Hat G d)): Audio p∈ Load G d (1+d):= by unfold Audio; exact Submodule.sum_mem _ fun i _=> by rw [C_mul']; exact Submodule.smul_mem _ _ (higher coin (Nat.add_le_add_left (Nat.le_of_lt_succ i.1.isLt) 1) (gated coin (coin i) (isWeightedHomogeneous_X ..)))
def overture (d:ℕ): Stamp G →ₐ[ℂ] Cap G d:= MvPolynomial.aeval (fun i=> Audio (ram (G:=G) i ∘ₗ scenic d))
lemma music_at (p:Stamp G)(X:Hat G d): view X (overture d p)=pit (scenic _ X) p:=by
  suffices h: (view X).comp (overture d)=pit (scenic _ X) from DFunLike.congr_fun h p; ext1 i; rw [AlgHom.comp_apply,overture,aeval_X,audio_at]; symm; exact aeval_X ..
lemma composed (d:ℕ)(p:Line G): overture d (harp p)=Audio (probe p ∘ₗ scenic d):= sameCap fun x=> by rw [music_at,leg_test,audio_at];rfl
lemma constant_low (w:I→ℕ)(n)(p:ℂ): C p∈ weightBound w n:= higher w (Nat.zero_le _) (gated w 0 (isWeightedHomogeneous_C w p))
theorem recorder (d:ℕ){p:Tile G} (X:Book G n p):∀ x, overture d (p x)∈ Load G d (n*(1+d)):= by
  induction X with
  | zero => exact fun x=> by rw [Pi.zero_apply,map_zero]; exact Submodule.zero_mem _
  | unit => exact fun x=> by simp only [Pi.one_apply,map_one]; simpa using constant_low (coin (d:=d) (G:=G)) (0*(1+d)) 1
  | left p=> exact fun x=> by rw [composed]; apply higher _ _ (auditory _); exact le_mul_of_one_le_left (Nat.zero_le _) (by unfold Fee.cost; omega)
  | right p=> exact fun x=> by rw [composed]; apply higher _ _ (auditory _); exact le_mul_of_one_le_left (Nat.zero_le _) (by unfold Fee.cost; omega)
  | rent p q=> exact fun x=> by rw [show ∀ c:ℂ, overture (G:=G) d (C c) = C c from fun c=> MvPolynomial.algHom_C ..]; apply constant_low
  | mul h p ih iu => exact fun x=> by rw [Pi.mul_apply,map_mul,add_mul]; exact bounds_mul coin (ih x) (iu x)
  | add h p ih iu => exact fun x=> by rw [Pi.add_apply,map_add]; exact Submodule.add_mem _ (ih x) (iu x)
  | scale p l ih => exact fun x=> by rw [Pi.smul_apply,map_smul]; exact Submodule.smul_mem _ l (ih x)
end YM.XSpace.Lows
