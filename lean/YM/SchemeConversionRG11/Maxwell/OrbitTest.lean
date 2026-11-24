import YM.SchemeConversionRG11.Maxwell.Ridges

/-!
# Read families on the actual shell, along a real matrix (mixing colors)

Laplacian on the finite matrix variables computes a finite family of `muted_pass`es.
Do not infer orbit equality on arbitrary off-shell Lie generators.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped Topology BigOperators ComplexOrder

variable {G : Gauge} {n m k l : ℕ}

abbrev Pct (G : Gauge) := G.ColorIndex × G.ColorIndex
abbrev Studio (G : Gauge) := EuclideanSpace ℝ (Pct G)
abbrev Wall (G : Gauge) := MvPolynomial (Pct G) ℂ

/-- Color transformation reading actual shell elements. -/
def graphL (b : Studio G) : G.Color →L[ℝ] G.Color := ∑ i : Pct G, b i • tint (unitColor G i.1) ∘L cp i.2 -- prec
lemma graph_eq (b : Studio G) (v : G.Color) : graphL b v=∑ i:Pct G,b i • v i.2 • unitColor G i.1 := by
  unfold graphL; rw [sum_apply]; rfl
lemma shell_graph (b : Studio G) (A : TaylorTower G) (k : ℕ) : faceMap k (graphL b) (A k) =
    ∑ i:Pct G,b i • fill k (unitColor G i.1) (faceMap k (cp i.2) (A k)) := by
  apply Subtype.ext; rw [AddSubmonoidClass.coe_finsetSum]; funext u v; ext1 z; simp only [SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,sum_apply,smul_apply]; change graphL b _ = _; rw [graph_eq]; rfl

def leave (A : TaylorTower G) (i : Slot G) (j : Pct G) := coordinateLeg i (fill i.1 (unitColor G j.1) (faceMap i.1 (cp j.2) (A i.1)))

def spray (A : TaylorTower G) : WickPol G →ₐ[ℂ] Wall G := aeval fun i:Slot G ↦ ∑ j:Pct G, X j*C (↑(leave A i j):ℂ)
def mix (b : Studio G) (A : TaylorTower G) : TaylorTower G := fun i ↦ faceMap i (graphL b) (A i)
def attract (b : Studio G) : Pct G → ℂ := fun i ↦ (b i:ℂ)

lemma spray_read (b : Studio G) (A : TaylorTower G) (p : WickPol G) : aeval (attract b) (spray A p)= Maxwell.probe (mix b A) p := by
  induction p using MvPolynomial.induction_on with
  | C => simp [spray,Maxwell.probe]
  | add _ _ hp hq => rw [map_add,map_add,map_add,hp,hq]
  | mul_X p i h =>
    rw [map_mul,map_mul,map_mul,h]; congr 1
    simp only [spray,map_sum,map_mul,aeval_X,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,Maxwell.probe]
    change _ = (↑(coordinateLeg i (faceMap i.1 (graphL b) (A i.1))):ℂ)
    rw [shell_graph b A i.1,map_sum]; simp only [map_smul,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]; rfl
lemma spray_none (A : TaylorTower G) (p : WickPol G) : aeval (0:Pct G→ℂ) (spray A p)=aeval (0:Slot G→ℂ) p := by
  induction p using MvPolynomial.induction_on with
  | C => simp [spray]
  | add _ _ hp hq => rw [map_add,map_add,map_add,hp,hq]
  | mul_X p i h => rw [map_mul,map_mul,map_mul,h]; congr 1; simp [spray]

def urn (A : TaylorTower G) (i : G.ColorIndex) (k : ℕ) : Echo k := Complex.ofRealCLM.toLinearMap.comp (Module.Dual.eval ℝ (Sheet k) (faceMap k (cp i) (A k)))
def expose (A : TaylorTower G) (N : ℕ) (i : Pct G) : Derivation ℂ (WickPol G) (WickPol G) :=
  ∑ k∈Finset.range (N+1),rip (urn A i.2 k) i.1

lemma exposing (A : TaylorTower G) {p : WickPol G} (N : ℕ) (h : p ∈ shelf G N) (i : Pct G) : pderiv i (spray A p) = spray A (expose A N i p) := by
  classical
  rw [Subalgebra.mem_toSubmodule] at h
  change p ∈ Algebra.adjoin ℂ (X '' _) at h
  induction h using Algebra.adjoin_induction with
  | mem p h =>
    obtain ⟨⟨k,a⟩,hk,rfl⟩ := h
    let e := keyAt (G:=G) k a
    rw [expose, derivation_sum_apply, Finset.sum_eq_single_of_mem k (Finset.mem_range_succ_iff.mpr (show k ≤ N from hk)) (fun b _ hb ↦ rip_off _ _ _ hb.symm), rip_same (k:=k)]
    unfold spray; rw [aeval_X,map_sum,algHom_C]
    simp_rw [mul_comm _ (C _),pderiv_C_mul]; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · rw [pderiv_X_self,mul_one]; rfl
    intro b _ hb; rw [pderiv_X_of_ne hb,mul_zero]
  | algebraMap => simp [spray] -- check
  | add p q _ _ hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
  | mul p q _ _ hp hq => rw [map_mul,Derivation.leibniz,Derivation.leibniz,hp,hq]; simp [smul_eq_mul]

/-- Evaluate all fields at chosen shell positions. -/
def mist (A : Fin n → TaylorTower G) : MultilinearMap ℂ (fun _ : Fin n ↦ WickPol G) (Wall G) :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Wall G)).compLinearMap fun i ↦ (spray (A i)).toLinearMap
lemma mist_read (A : Fin n → TaylorTower G) (W : Fin n → WickPol G) (b : Studio G) :
    aeval (attract b) (mist A W)=∏ i, Maxwell.probe (mix b (A i)) (W i) := by change aeval _ (∏ i,spray _ _) = _; rw [map_prod]; simp_rw [spray_read]

lemma derive_product (p : Fin n → Wall G) (j : Pct G) : pderiv j (∏ i,p i)= ∑ i:Fin n,∏ a, update p i (pderiv j (p i)) a := by
  have hd (s : Finset (Fin n)) : pderiv j (∏ i∈s,p i)= ∑ i∈s, ∏ a∈s, update p i (pderiv j (p i)) a := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, pderiv_mul, ih,Finset.sum_insert hi,Finset.prod_insert hi,update_self]; congr 1
      · congr 1; exact Finset.prod_congr rfl fun a ha ↦ by rw [update_of_ne (ne_of_mem_of_not_mem ha hi)]
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a ha ↦ ?_; rw [Finset.prod_insert hi, update_of_ne (Ne.symm (ne_of_mem_of_not_mem ha hi))]
  exact hd Finset.univ

lemma mist_derive (A : Fin n → TaylorTower G) (W : Fin n → WickPol G) (N : ℕ) (h : ∀ i,W i∈ shelf G N) (j : Pct G) :
    pderiv j (mist A W) = ∑ i:Fin n,∑ k∈Finset.range (N+1),mist A (hit (urn (A i) j.2 k) j.1 i W) := by
  let B i := spray (A i) (W i)
  change pderiv j (∏ i:Fin n,B i) = _; rw [derive_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [show B i=spray (A i) (W i) from rfl, exposing (A i) _ (h i)]
  rw [show (∏ a, update B i (spray (A i) (expose (A i) N j (W i))) a)=mist A (update W i (expose (A i) N j (W i))) from ?_,expose, derivation_sum_apply,MultilinearMap.map_update_sum]; try rfl
  change _ = ∏ a : Fin n, spray (A a) (update W i (expose _ _ _ _) a)
  exact Finset.prod_congr rfl fun a _ ↦ by rcases eq_or_ne a i with rfl|ha <;> first | rw [update_self,update_self] | (rw [update_of_ne ha,update_of_ne ha])
lemma twice_mist (A : Fin n → TaylorTower G) (W : Fin n → WickPol G) (N : ℕ) (h : ∀ i,W i∈ shelf G N) (j : Pct G) :
    pderiv j (pderiv j (mist A W)) = ∑ i:Fin n,∑ k∈Finset.range (N+1),∑ a:Fin n,∑ l∈Finset.range (N+1),mist A (hit (urn (A a) j.2 l) j.1 a (hit (urn (A i) j.2 k) j.1 i W)) := by
  rw [mist_derive A W N h j]; simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k hk ↦ mist_derive A _ N ?_ _
  intro a; unfold hit; rcases eq_or_ne a i with rfl|ha; · rw [update_self]; exact rip_shelf _ _ _ (h a)
  rw [update_of_ne ha]; exact h a

def snow {ι : Type*} [Fintype ι] (p : ι → ℂ) (W : Panel ι n G) (A : Fin n → TaylorTower G) := ∑ i, p i • mist A (W i)

/-- Positive-sign symbol Laplacian for taking ball mean. -/
def hot (ι : Type*) [Fintype ι] : Module.End ℂ (MvPolynomial ι ℂ) := ∑ i:ι,(pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap
lemma hot_read {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℂ) : hot ι p=∑ i, pderiv i (pderiv i p) := by unfold hot; rw [LinearMap.sum_apply]; rfl

universe z
lemma powered (C₀ : G.ColorIndex) (k : ℕ) : ∀ {ι : Type z} [Fintype ι] {p : ι→ℂ} {W : Panel ι n G}, Muted p W →
    ∀ (A : Fin n → TaylorTower G), aeval (0:Pct G→ℂ) ((hot (Pct G)^k) (snow p W A))=0 := by
  classical
  induction k with
  | zero =>
    intro ι t p W h A
    rw [pow_zero]; change aeval _ (∑ i,p i • ∏ j,spray (A j) (W i j))=_
    rw [map_sum]; simp_rw [map_smul,map_prod,spray_none]; exact muted_ice h
  | succ k ih =>
    intro ι t p W h A
    let L := (aeval (R:=ℂ) (0:Pct G→ℂ)).toLinearMap.comp (hot (Pct G)^k)
    obtain ⟨v,hv⟩ := shelf_frame W
    rw [pow_succ]; change L (hot (Pct G) (snow p W A))=_
    let H (a b : G.ColorIndex) := pderiv (a,b) (pderiv (a,b) (snow p W A))
    rw [hot_read,Fintype.sum_prod_type, Finset.sum_comm]
    change L (∑ b:G.ColorIndex, ∑ a:G.ColorIndex,H a b)=0
    rw [map_sum]; apply Finset.sum_eq_zero; intro b _
    let S i k := urn (A i) b k
    let R (a:G.ColorIndex) (i : Fin n) (k : ℕ) (j : Fin n) (l : ℕ) (u : ι) := p u • mist A (hit (S j l) a j (hit (S i k) a i (W u)))
    let B:=Finset.range (v+1)
    have he (a) : H a b=∑ i : Fin n,∑ k∈B,∑ j : Fin n,∑ l∈B,∑ u : ι,R a i k j l u := by
      unfold H snow; simp_rw [map_sum,Derivation.map_smul,twice_mist A _ v (hv _) (a,b),Finset.smul_sum]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]
    have ht (i r j l) : L (∑ a:G.ColorIndex,∑ u : ι,R a i r j l u)=0 := by
      have he := ih (muted_pass C₀ h (S i r) (S j l) i j) A
      unfold snow at he; rw [Fintype.sum_prod_type, Finset.sum_comm] at he; exact he
    simp_rw [he]
    rw [Finset.sum_comm,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [Finset.sum_comm,map_sum]; apply Finset.sum_eq_zero; intro u _
    rw [Finset.sum_comm,map_sum]; apply Finset.sum_eq_zero; intro j _; rw [Finset.sum_comm,map_sum]; apply Finset.sum_eq_zero; intro l _; exact ht ..

end YM.SchemeConversionRG11.Corona
