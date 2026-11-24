import YM.XSpace.Seats

/-!
# Any exterior layout: acceptance by finite interpolate of charges

Symbols have uniform degree, but can have arbitrary numbers of support variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Function Filter Set Lattice Lows Scale Mu Trace Chart2 MvPolynomial Next.Rank.Normal Contraction Finsupp Future Litter
open scoped Topology BigOperators ContDiff
variable {ι Z I V : Type*} {G:Gauge} {K: Filter ι} {k d n:ℕ}

abbrev DegZ (V:Type*) (n:ℕ):= weightBound (fun _:V=>1) n
lemma degreeAny (p:poly I): ∃ n,p∈DegZ I n:= cap_known _ p
lemma sustains {L:poly I →ₐ[ℂ]poly Z} (h:∀ i, L (X i)∈ DegZ Z 1) {p:poly I} (hp:p∈ DegZ I k): L p∈DegZ Z k :=by
  have he (i:I→₀ℕ)(c:ℂ): L (monomial i c)∈DegZ Z (Finsupp.weight (fun _:I=>1) i):=by
    classical apply Extra.FD.per_factor i; change L (C c)∈_; rw [map_zero,MvPolynomial.algHom_C]; apply constant_low
    intro p a hp; rw [map_add, weight_single, one_smul,monomial_add_single,pow_one,map_mul]; exact bounds_mul _ hp (h a)
  classical rw [p.as_sum,map_sum]; exact Submodule.sum_mem _ fun i hi=> higher _ ((bounded _).mp hp i hi) (he ..)
lemma name_charge {p:poly I} (h:p∈DegZ I k)(u:I→ V): rename u p∈ DegZ V k:=by apply sustains _ h; intro i; rw [rename_X]; exact gated _ 1 (isWeightedHomogeneous_X ..)
lemma steadied {p:Word G}(h:p.length=n): story p∈DegZ (Outline.Bone G ℤ) n:= by
  subst n; induction p with
  | nil=> change 1∈_; exact gated _ _ (isWeightedHomogeneous_one ..)
  | cons i p IH=> rw [read_word,List.length_cons,add_comm p.length]; apply bounds_mul _ _ IH; unfold harp glyph; rw [linearCombination_apply,Finsupp.sum]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (gated _ _ (isWeightedHomogeneous_X ..))

private abbrev Ray (n:ℕ):= ↥(DegZ Unit n)
private instance (n:ℕ): FiniteDimensional ℂ (Ray n):= by
  let f:=fun _:Unit=> (1:ℕ); letI:= (finite_of_nat_weight_le f (fun _=> one_ne_zero) n).to_subtype; exact Module.Finite.of_basis (basisRestrictSupport ℂ {i:Unit→₀ℕ|weight f i ≤ n})

private def tix (t:ℝ) : poly Unit→ₐ[ℂ]ℂ:= aeval fun _=>(t:ℂ)
private lemma tix_e {p:Ray n}(h:∀ i:ℝ,tix i p.val=0):p=0:=Subtype.ext (MvPolynomial.funext_set (fun _=> Set.range ((↑):ℝ→ℂ)) (fun _=> infinite_range_of_injective Complex.ofReal_injective) (fun y he=>by obtain ⟨u,hu⟩:= he () (mem_univ _); rw [show y=fun _=>(u:ℂ) from funext fun x=> by cases x; exact hu.symm]; exact (h u).trans (map_zero _).symm))
private def echo (A B:Contact G) : Mu.Stamp G →ₐ[ℂ] poly Unit:= aeval fun i=> C (numbers A i)+ C (numbers B i) * X ()
private lemma echo_value (A B:Contact G)(p:Mu.Stamp G)(t:ℝ):pit (A+t • B) p=tix t (echo A B p):=by
  suffices h:(tix t).comp (echo A B)=pit (A+t • B) from (DFunLike.congr_fun h p).symm; ext1 i; simp [pit, echo,tix,numbers]; ring
private lemma echo_bound (A B: Contact G){p:Mu.Stamp G}(h:p∈DegZ (UnitIndex G) k): echo A B p∈ DegZ Unit k:=by
  apply sustains _ h; intro i; rw [echo,aeval_X,C_mul']; exact Submodule.add_mem _ (constant_low ..) (Submodule.smul_mem _ _ (gated _ _ (isWeightedHomogeneous_X ..)))
-- fixed coefficients
lemma views (n:ℕ):∃ (s:Finset ℝ)(u:s→ℂ),∀ (A B: Contact G) (p:Mu.Stamp G), p ∈ DegZ (UnitIndex G) n→ pit A (part B p)=∑ i:s,u i * pit (A+i.val • B) p :=by
  let f t:Module.Dual ℂ (Ray n):= (tix t).toLinearMap ∘ₗ (DegZ Unit n).subtype
  let D: Module.Dual ℂ (Ray n):=(tix 0).toLinearMap ∘ₗ (slit (fun _:Unit=>(1:ℂ))).toLinearMap ∘ₗ (DegZ Unit n).subtype
  obtain ⟨s,v,h⟩:= Future.bought f (fun p hp=> tix_e hp); refine ⟨s,(fun i=> D (v i)),?_⟩; intro A B p hp; let w:Ray n:=⟨echo A B p, echo_bound A B hp⟩
  have he:= directional A B p; simp_rw [echo_value A B] at he
  change pit A (Chart2.D B p)=_; rw [he.unique (show HasDerivAt (fun t=>tix t w.val) (D w) 0 from ?_)]; conv_lhs=>arg 2; rw [h w]; skip
  · rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,smul_eq_mul,echo_value]; exact mul_comm ..
  apply Chart2.slit_shift (f:=fun t:ℝ=>fun _:Unit=>(t:ℂ)); intro _; have he:=Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ)); rw [Complex.ofRealCLM_apply, Complex.ofReal_one] at he; exact he

abbrev Scalar (ι Y:Type*) := ι→Y→ℂ
abbrev Club (G:Gauge)(ι:Type*) := Submodule ℝ (ι→ Contact G)
abbrev Accepts (ι Y:Type*) := Submodule ℂ (Scalar ι Y)
variable (N: Accepts ι Z)(C:Club G ι)
def Admits (p:ι→ Z→ Mu.Stamp G):Prop := (∃ n,∀ i x,p i x∈ DegZ (UnitIndex G) n)∧ ∀ v∈C,(fun i x=> pit (v i) (p i x))∈N
lemma admit_steps {p:ι→ Z→ Mu.Stamp G}(h:Admits N C p){v:ι→ Contact G}(H:v∈C): Admits N C (fun i x=> D (v i) (p i x)):=by
  obtain ⟨n,he⟩:=h.1; refine ⟨⟨n,fun i x=> slit_bound _ _ (he i x)⟩,fun A HA=>?_⟩
  obtain ⟨s,w,P⟩:= views (G:=G) n
  generalize hw : (fun i x=> pit (A i) (D (v i) (p i x))) = f
  rw [show f=∑ i:s,w i • (fun j y=> pit ((A+i.val • v) j) (p j y)) from ?_]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (h.2 _ (C.add_mem HA (C.smul_mem _ H)))
  rw [← hw]; funext i x; rw [Finset.sum_apply, Finset.sum_apply]; exact P _ _ _ (he i x)
end YM.XSpace.Stall
