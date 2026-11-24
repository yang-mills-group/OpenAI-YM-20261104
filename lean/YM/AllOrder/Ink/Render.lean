import YM.AllOrder.Ink.Gather
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Rail
variable (F:Field α) (H: F.Good a C k) (ht:0<a)
local notation "I"=> Leaf n α
local notation "P"=>rule α n
lemma mantle_pos (N k:ℕ):0< mantle N k:= (pullC_pos 0 k).trans_le (can_pull 0 k N (Nat.zero_le N))
include H ht
lemma ride (z:Site n)(N:ℕ): Beacon (Prod.fst : Leaf n α→Site n) (widthG a N) N (F.site n z) z 0 (mantle N k*C) := by
  intro i hi p; rw [←(H.tests ht.le z (codeL p k)).tsum_eq]; let c:= mantle N k; let f (v:F.Ty):= entry (invoice z (F.slip v)) 0 p; let V:= Real.exp (-widthG a N * spanSites Prod.fst z p); have he:= Real.exp_pos (-widthG a N* spanSites Prod.fst z p); change ‖∑' i,F.fee i*f i‖≤ _
  have hl:= mantle_pos N k; let u(v:F.Ty) :=‖F.fee v *f v‖; have hQ: SumBudget u ((c*V)*C):= by
    apply budget_mono (budget_scale (f:=F.price a) (mul_pos hl he).le H.pay); · exact fun v=>norm_nonneg _
    intro v; unfold u; rw [norm_mul]; refine (mul_le_mul_of_nonneg_left (horizon z (F.slip v) k (H.length v) p hi ht) (norm_nonneg (F.fee v))).trans_eq ?_; unfold Field.price; rw [Real.norm_eq_abs]; ring
  exact (norm_tsum_le_tsum_norm hQ.2.1).trans (hQ.2.2.trans_eq (mul_right_comm c V C))
omit [Fintype α] H ht in
lemma shorter [Fintype α] (_H:F.Good a C k) (ht:0<a) (N:ℕ): 0<weaker N (widthG a N):= by have h:=widthG_pos (k:=N) ht; unfold weaker; positivity
def gift (k:ℕ)(C a:ℝ)(N:ℕ):= (mantle N k*C)*countCost (widthG a N/2)
omit H in
lemma gift_nn (ha:0≤C) (k N:ℕ): 0≤gift k C a N:= mul_nonneg (mul_nonneg (mantle_pos N k).le ha) (count_pos (half_pos (widthG_pos ht))).le
def labelT (A : Money.Bills α)(k:ℕ)(n:Side):= extractF (iteratedFDeriv ℝ (k+1) (A n) 0)
def labelW (F:Field α)(k : ℕ):= labelT (F.table) k
lemma scatter_fee (N:ℕ): Scatter (E:=ℝ) (Prod.fst : Leaf n α→Site n) (weaker N (widthG a N)) N (F.table n) 0 (gift k C a N):= by
  rw [show F.table n=(fun z=>∑ i:Site n,F.site n i z) from funext (Field.table_apply F)]
  have hc(i:Site n):= (H.site ht.le i).2.1.read.smooth; have hb:= scatter (E:=ℝ) (y:=id) (ι:=Leaf n α) (Multiplicity.injective Function.injective_id) (fun i=>(hc i).contDiffAt (x:=0)) (fun i=> ride F H ht i N) (widthG_pos ht) (mul_nonneg (mantle_pos N k).le H.nonneg)
  rw [Nat.cast_one,mul_one] at hb; exact hb
omit H ht in
lemma shapes (F:rule α n→ℝ) (hF : Scatter (Prod.fst:Leaf n α→Site n) a (M+1) F 0 C): Room (extractF (iteratedFDeriv ℝ (M+1) F 0)) a C:= by
  intro i t; let j : Fin (M+1)→ Leaf n α:= Fin.cons i t; have he:= hF (M+1) le_rfl j 0
  rw [show (spanSites Prod.fst (j 0).1 j)=_ from (show spanSites Prod.fst (j 0).1 j=∑ k:Fin M,separation i.1 (t k).1 by simp [spanSites,j,Fin.sum_univ_succ])] at he; exact he
open Further.PhysicalPeriodLimitF933 Shingle Macrame
omit H ht in
lemma jetsKeep {F: Money.Bills α}(h:∀ n,ContDiffAt ℝ ω (F n) 0) (k:ℕ) (hx:∀ n m,∀ M,∀ W: Window n m M,∀ x:rule α n,F m (convey W x)=(M:ℝ)*F n x) : Keep (labelT F k) (fun _=>True):= by
  have hp(n m:Side)(M:ℕ)(W: Window n m M): pilots W (iteratedFDeriv ℝ (k+1) (F n) 0) (iteratedFDeriv ℝ (k+1) (F m) 0):= flight W (h n) (h m) (Eventually.of_forall (hx n m M W))
  have hv(n:Side)(w:Site n):= hp n n 1 (Macrame.parallel w); exact ⟨fun n _=> pilots.still (hv _),fun n m _ _ t h=> cooks (Macrame.normal ⟨t,h⟩ h) (pow_pos (Nat.pos_of_mul_pos_left (show 0<n.val*t from h ▸ m.property)) _) (hp _ _ _ _) (hv m)⟩
lemma endless (r:ℕ) : let a':= weaker (r+1) (widthG a (r+1)); ∃ G: Fan α α r, Cap G (small_a a') (gift k C a (r+1)*boltC r a') ∧∀ n,labelW F r n=pieces G n := by
 let h:= obtain_fan (a:=weaker (r+1) (widthG a (r+1))) (C:=gift k C a (r+1)) (⟨0,fun n _=>trivial⟩:Often (fun _=>True)) (jetsKeep (fun n=> (H.binding ht.le (n:=n)).2.1.read.smooth.contDiffAt) r (fun _ _ _ W=> fun x=>Echo.pay W F x)); let t:= shorter F H ht (r+1); intro z; obtain ⟨g,hg,hV⟩:= h (fun n _=> shapes _ (scatter_fee F H ht (n:=n) (r+1))) t (gift_nn ht (C:=C) H.nonneg ..); exact ⟨g,hg,fun n=> hV n trivial⟩
end Rail
end YM.AllOrder.Ink
