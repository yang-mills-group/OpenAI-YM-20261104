import YM.XSpace.Lows

/-!
# Bookkeeping for projection costs on finite exposures
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Future
open Function Filter Set FiniteDimensional
open scoped Topology BigOperators
variable {K I T V V' F:Type*}{L:Filter I}
def Likely [TopologicalSpace T] (L:Filter I)(f:I→T): Prop:= ∃ t,Tendsto f L (𝓝 t)
namespace Likely
lemma congr {T:Type*}[TopologicalSpace T]{f g:I→T}(h:Likely L f)(p:f=ᶠ[L]g):Likely L g:= by obtain ⟨c,hc⟩:=h; exact ⟨_,hc.congr' p⟩
lemma cont [TopologicalSpace T][TopologicalSpace K]{f:I→T}{g:T→K}(h: Likely L f)(h':Continuous g): Likely L (fun i=>g (f i)):= by obtain ⟨c,h⟩:=h; exact ⟨_,h'.continuousAt.tendsto.comp h⟩
lemma add [TopologicalSpace T][Add T][ContinuousAdd T]{f g:I→T}(h:Likely L f)(p:Likely L g):Likely L (fun i=>f i+g i):= by obtain ⟨x,h⟩:=h; obtain ⟨y,p⟩:=p; exact ⟨_, h.add p⟩
lemma mul [TopologicalSpace T][Mul T][ContinuousMul T]{f g:I→T}(h:Likely L f)(p:Likely L g):Likely L (fun i=>f i*g i):= by obtain ⟨x,h⟩:=h; obtain ⟨y,p⟩:=p; exact ⟨_, h.mul p⟩
lemma smul [TopologicalSpace T][SMul K T][TopologicalSpace K][ContinuousSMul K T]{f:I→K}{g:I→T}(h:Likely L f)(p:Likely L g):Likely L (fun i=>f i • g i):= by obtain ⟨x,h⟩:=h; obtain ⟨y,p⟩:=p; exact ⟨_, h.smul p⟩
lemma sub [TopologicalSpace T][AddGroup T][IsTopologicalAddGroup T]{f g:I→T}(h:Likely L f)(p:Likely L g):Likely L (fun i=>f i-g i):= by obtain ⟨x,h⟩:=h; obtain ⟨y,p⟩:=p; exact ⟨_, h.sub p⟩
lemma zero [TopologicalSpace T][Zero T]:Likely L (fun _=>(0:T)):= ⟨_,tendsto_const_nhds⟩
lemma const [TopologicalSpace T](L:Filter I)(x:T):Likely L (fun _=>x):= ⟨_,tendsto_const_nhds⟩
lemma sum [TopologicalSpace F][AddCommMonoid F][ContinuousAdd F](p:T→I→F)(s:Finset T)(h:∀ i∈s,Likely L (p i)): Likely L (fun i=>∑ k∈s,p k i):= by
  classical induction s using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; apply zero | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact add (h i (by simp)) (ih fun j hj=> h j (by simp [hj]))
lemma bound [NormedAddCommGroup F]{p:I→F}(h:Likely L p): ∃ C:ℝ,0≤C∧∀ᶠ i in L,‖p i‖≤C:= by obtain ⟨c,h⟩:=h; exact ⟨‖c‖+1,by positivity,h.norm.eventually (ge_mem_nhds (lt_add_one _))⟩
end Likely

variable [NontriviallyNormedField K][AddCommGroup V][Module K V][AddCommGroup V'][Module K V']
abbrev reads (K V:Type*) [NontriviallyNormedField K][AddCommGroup V][Module K V] := Module.Dual K V
def By (K: Type*)[NontriviallyNormedField K][Module K V] (L:Filter I)(p:I→V)(x:V):Prop:= ∀ T:reads K V,Tendsto (fun i=> T (p i)) L (𝓝 (T x))
def Still (K: Type*)[NontriviallyNormedField K][Module K V](L:Filter I)(p:I→V): Prop:= ∃ x, By K L p x

section Select
variable [FiniteDimensional K V]
private lemma buy (f:T→ reads K V)(h:∀ x,(∀ t,f t x=0)→x=0) : ∃ (s:Finset T)(F:(s→K)→ₗ[K] V),∀ x:V, F (fun i=> f i.val x)=x:=by
  classical
  let A (s:Finset T) : V→ₗ[K](s→K):= LinearMap.pi (fun i:s=> f i.val); let B (s:Finset T):=Module.finrank K (LinearMap.ker (A s)); let p (n:ℕ):= ∃ s,B s=n; have he : ∃ n,p n:= ⟨_,∅,rfl⟩
  obtain ⟨s,hs⟩:= (show p (Nat.find he) from Nat.find_spec he)
  have hZ: LinearMap.ker (A s)=⊥:=by
    apply le_antisymm _ bot_le; intro x hx; rw [Submodule.mem_bot]
    apply h; intro t; have hh: LinearMap.ker (A (insert t s))=LinearMap.ker (A s):= Submodule.eq_of_le_of_finrank_le (fun v h=> show (A s) v=0 from funext fun i=>congr_fun (show A (insert t s) v=0 from h) ⟨i.val,Finset.mem_insert_of_mem i.property⟩) (show B s ≤ B (insert t s) by rw [hs]; exact Nat.find_min' he ⟨_,rfl⟩)
    exact congr_fun (show A (insert t s) x=0 from (show x∈ LinearMap.ker (A (insert t s)) from hh.symm ▸ hx)) ⟨_,Finset.mem_insert_self ..⟩
  obtain ⟨F,h⟩:= (A s).exists_leftInverse_of_injective hZ; exact ⟨s,F, LinearMap.congr_fun h⟩
-- explicit interpolation; reconstruction of all text, no equivalent norm assumption
lemma bought (f:T→ reads K V)(h:∀ x,(∀ t,f t x=0)→x=0) : ∃ (s:Finset T)(u:s→ V),∀ x:V,x = ∑ i:s, f i.val x • u i:=by
  classical
  obtain ⟨s,F,H⟩:= buy f h; let b i:=F (Pi.single i 1); refine ⟨s,b,fun x=>?_⟩; conv_lhs=>rw [← H x, show (fun i:s=>f i.val x) = ∑ j:s, f j.val x • Pi.single j 1 from funext fun i=> by rw [Finset.sum_apply]; simp [Pi.single_apply],map_sum]
  exact Finset.sum_congr rfl fun i _=> map_smul F _ _
lemma redeem (f:T→ reads K V)(h:∀ x,(∀ t,f t x=0)→x=0){A:I→V}(H:∀ x,Likely L fun i=> f x (A i)) : Still K L A:=by
  classical obtain ⟨s,u,hu⟩:= bought f h; choose C hc using H; let x':= ∑ i:s,C i.val • u i; refine ⟨x',fun x=> ?_⟩
  have hp:= tendsto_finsetSum Finset.univ fun (i:s) _=> (hc i.val).smul_const (x (u i)); rw [show x x'= ∑ i:s,C i.val • x (u i) from map_sum x _ _ |>.trans (Finset.sum_congr rfl fun _ _=>map_smul x _ _)]
  refine hp.congr (fun i=> ?_); symm; conv_lhs=> rw [hu (A i),map_sum]
  exact Finset.sum_congr rfl fun j _=> map_smul x _ _
lemma redeemBy (f:T→ reads K V)(h:∀ x,(∀ t,f t x=0)→x=0){A:I→V}{x:V} (H:∀ j,Tendsto (fun i=> f j (A i)) L (𝓝 (f j x))):By K L A x:=by
  classical obtain ⟨s,u,hu⟩:= bought f h; intro Q; let v(j:s):= Q (u j); have he(x:V):Q x=∑ j:s,f j.val x • v j:=by conv_lhs=> rw [hu x,map_sum]; simp only [map_smul]
  simp_rw [he]; exact tendsto_finsetSum _ fun i _=> (H i.val).smul_const _
def TestBound (K: Type*) [NontriviallyNormedField K][Module K V](w:I→ℝ)(A:I→V):Prop:=∀ f:reads K V,∃ C:ℝ,0≤C∧∀ i,‖f (A i)‖ ≤ C*w i
lemma coupon (f:T→ reads K V)(h:∀ x,(∀ t,f t x=0)→x=0){A:I→V}{w:I→ℝ}(H:∀ t,∃ C:ℝ,0≤C∧∀ i, ‖f t (A i)‖≤ C*w i):TestBound K w A:=by
  classical obtain ⟨s,u,hu⟩:= bought f h; choose C hc H using H; intro p; refine ⟨∑ i:s, C i.val* ‖p (u i)‖,Finset.sum_nonneg fun i _=> by positivity [hc i.val],fun i=>?_⟩
  rw [hu (A i),map_sum,Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>by rw [map_smul,norm_smul, mul_right_comm (C j.val) _ (w i)]; exact mul_le_mul_of_nonneg_right (H _ i) (norm_nonneg _))
end Select

lemma translateBy (f:V→ₗ[K] V'){A:I→V}{x:V} (h:By K L A x): By K L (fun i=> f (A i)) (f x):= fun g=> h (g ∘ₗ f)
lemma translate (f:V→ₗ[K] V'){A:I→V}(h:Still K L A):Still K L fun i=>f (A i):= by obtain ⟨x,h⟩:=h; exact ⟨f x,translateBy f h⟩
lemma receive {p:I→V}(h:Still K L p)(f:reads K V):Likely L fun i=>f (p i):=by obtain ⟨x,h⟩:=h; exact ⟨f x,h f⟩
lemma send [FiniteDimensional K V]{p:I→V}(h:Still K L p)(g:I→ reads K V)(H:∀ x:V,Likely L fun i=>g i x): Likely L fun i=>g i (p i):=by
  classical let f:=Module.finBasis K V
  have he(i:I):g i (p i) = ∑ j,f.coord j (p i) • g i (f j):= by
    conv_lhs=> rw [← f.sum_repr (p i), map_sum]; simp only [map_smul]
    simp [Module.Basis.coord_apply]
  simp_rw [he]; exact Likely.sum _ Finset.univ fun j _=> (receive h (f.coord j)).smul (H _)
end YM.XSpace.Future
