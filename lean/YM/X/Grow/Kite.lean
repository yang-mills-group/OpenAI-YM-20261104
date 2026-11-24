import YM.X.Grow.Solid
import YM.Next.MAXWELL.Algebra
/-!
# Tower-index functions with actual real variables of weight (n+1) at level n.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open MvPolynomial Function Lattice Next.Rank Normal LiftMark Maxwell Maxwell.Free Finset
open scoped Topology Classical Pointwise
section
variable (E:ℕ→Type*) [∀ n,AddCommGroup (E n)][∀ n,Module ℝ (E n)][∀ n,FiniteDimensional ℝ (E n)]
abbrev Pick (n:ℕ):= Fin (Module.finrank ℝ (E n))
abbrev Kite:= Σ n:ℕ, Pick E n
def owns (n:ℕ):= Module.finBasis ℝ (E n)
variable {E}
def probeL (x:(n:ℕ)→ E n): poly (Kite E) →ₐ[ℂ] ℂ:= MvPolynomial.aeval fun i: Kite E=> ((owns E i.1).coord i.2 (x i.1):ℂ)
def colorL (i:ℕ)(f:E i→ₗ[ℝ] ℝ):poly (Kite E):= ∑ j:Pick E i, (↑(f (owns E i j)):ℂ) • MvPolynomial.X ⟨i,j⟩
lemma eyes (x:(n:ℕ)→E n)(i:ℕ)(f:E i→ₗ[ℝ] ℝ): probeL x (colorL i f)=(f (x i):ℂ):= by
    unfold probeL colorL; conv_rhs=> rw [← (owns E i).sum_repr (x i)]
    simp only [map_sum,map_smul,smul_eq_mul, MvPolynomial.aeval_X,Complex.ofReal_sum,Complex.ofReal_mul]; exact sum_congr rfl fun k _=> mul_comm ..
def gear (E:ℕ→Type*) [∀ n,AddCommGroup (E n)][∀ n,Module ℝ (E n)] (i: Kite E):ℕ:= i.1+1 -- Kite defeq [∗Finite]? Pick uses not required
lemma gears (i:ℕ)(f:E i→ₗ[ℝ] ℝ):MvPolynomial.IsWeightedHomogeneous (gear E) (colorL i f) (i+1):= by
    unfold colorL; refine IsWeightedHomogeneous.sum _ _ _ (fun j _=> ?_); rw [← MvPolynomial.C_mul']; apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X .. 
lemma probe_ext {p q:poly (Kite E)}(h:∀ x:(n:ℕ)→E n,probeL x p=probeL x q):p=q:= by
    let m (i:Kite E):= Set.range Complex.ofReal; apply MvPolynomial.funext_set m (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective); intro v hv; choose f hf using fun i : Kite E=>show ∃t:ℝ,(t:ℂ)= v i from hv i (Set.mem_univ i); let k (n:ℕ):E n:= ∑ i:Pick E n, f ⟨n,i⟩ • owns E n i
    suffices he : ∀ i: Kite E, (↑((owns E i.1).coord i.2 (k i.1)):ℂ)=v i by rw [← funext he]; exact h k
    intro i; rcases i with ⟨n,i⟩; rw [← hf ⟨n,i⟩]; apply congr_arg; unfold k; dsimp only; rw [map_sum,Finset.sum_eq_single i]; · simp
    · intro j _ h; simp [h,h.symm, Finsupp.single_apply]
    · simp

variable {F:ℕ→Type*}[∀ n,AddCommGroup (F n)][∀ n,Module ℝ (F n)][∀ n,FiniteDimensional ℝ (F n)]
def localMap (f:(n:ℕ)→ E n→ₗ[ℝ] F n): poly (Kite F)→ₐ[ℂ] poly (Kite E) := MvPolynomial.aeval fun i: Kite F=> colorL i.1 ((owns F i.1).coord i.2 ∘ₗ f i.1)
lemma probe_map (f:(n:ℕ)→ E n→ₗ[ℝ] F n) (x:(n:ℕ)→E n)(p): probeL x (localMap f p)=probeL (fun n=> f n (x n)) p:= by
    apply DFunLike.congr_fun (f:=(probeL x).comp (localMap f)); ext1 i; rw [AlgHom.comp_apply,localMap,aeval_X,eyes]; simp [probeL]
end

lemma trimmer {V:Type*} {u:V→ℕ}{p:poly V}{n:ℕ}:level u n p= ∑ i∈range (n+1),weightedHomogeneousComponent u i p:= by
   ext x; change coeff x (Rise.trim p u n)=_; rw [Rise.trim_coeff, MvPolynomial.coeff_sum]; simp only [coeff_weightedHomogeneousComponent, sum_ite_eq, mem_range]; split_ifs <;> first|rfl|omega
lemma trimmer_hom {V:Type*}{u:V→ℕ}{p:poly V}{n k:ℕ}(h: k≤n)(hp:IsWeightedHomogeneous u p k): level u n p=p:= by
    rw [trimmer,sum_eq_single_of_mem k (mem_range.mpr (by omega)),hp.weightedHomogeneousComponent_same]; exact fun i _ hi=> hp.weightedHomogeneousComponent_ne i hi
lemma hom_feed {V W:Type*}{u:V→ℕ}{w:W→ℕ}{p:poly V}{n:ℕ}(F:poly V→ₐ[ℂ] poly W)(h:∀i,IsWeightedHomogeneous w (F (MvPolynomial.X i)) (u i))(hp:IsWeightedHomogeneous u p n): IsWeightedHomogeneous w (F p) n:= by
    rw [← hp.weightedHomogeneousComponent_same,←Maxwell.Free.commuting _ _ F h]; exact weightedHomogeneousComponent_mem .. -- name
lemma hom_commute {V W:Type*}{u:V→ℕ}{w:W→ℕ}{p:poly V}{n:ℕ}(F:poly V→ₐ[ℂ] poly W)(h:∀i,IsWeightedHomogeneous w (F (MvPolynomial.X i)) (u i)):level w n (F p)=F (level u n p):= by simp_rw [trimmer, Maxwell.Free.commuting _ _ F h,map_sum]
section
variable {E:ℕ→Type*} [∀ n,AddCommGroup (E n)][∀ n,Module ℝ (E n)][∀ n,FiniteDimensional ℝ (E n)]
variable {F:ℕ→Type*}[∀ n,AddCommGroup (F n)][∀ n,Module ℝ (F n)][∀ n,FiniteDimensional ℝ (F n)]
lemma local_hom (f:(n:ℕ)→ E n→ₗ[ℝ] F n)(i: Kite F):IsWeightedHomogeneous (gear E) (localMap f (MvPolynomial.X i)) (gear F i):= by rw [localMap,aeval_X]; exact gears (E:=E) _ _
lemma local_trim (f:(n:ℕ)→ E n→ₗ[ℝ] F n)(p)(k): level (gear E) k (localMap f p)=localMap f (level (gear F) k p):= hom_commute _ (local_hom f)
-- parity reality/conjugation via eval.
end
end YM.PositionX.Grow
