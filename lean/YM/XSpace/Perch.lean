import YM.XSpace.Weaving
/-!
# Chiral diagonal contacts and cross ledger at lags
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chiral Litter Mu Tide Scale Pages Sail Chart2 Finsupp MvPolynomial Source
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d e:ℕ}{H:Hol G}
def folds (σ τ:Bool)(p r:P)(a b:Axis):ℝ :=∑ i:Axis,q σ p a i*q τ r b i
lemma magnetism (σ τ:Bool)(p r:P): magnetic σ τ p r=∑ a:Axis,∑ b:Axis,folds σ τ p r a b • D a (η b Sail.cover):=by
  unfold magnetic drawn drawΦ; rw [ordered]; unfold field folds; simp_rw [_root_.map_sum,map_smul,Finset.smul_sum, smul_smul, Finset.sum_smul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
lemma folding (σ:Bool)(p r:P)(a b:Axis): folds σ σ p r a b= dot3 p r*dotI a b+ sig σ*∑ t:P,liftedSign p r t*q σ t a b:=by rw [folds]; simp_rw [show ∀ i:Axis,q σ r b i= -q σ r i b from fun i=> chosen_sqrt2 σ r i b,mul_neg,Finset.sum_neg_distrib,spec_algebra]; ring

def traceLag (p r:P)(a:Toe):Toe:= dot3 p r • lamp a
lemma down_eq (p:Toe)(a:Axis): D a (η a p) =η a (D a p):=by funext v; change p (v+step a-step a)-_-(p (v-step a)-_)=p (v-step a+step a)-_-(p (v+step a)-_); rw [sub_add_cancel,add_sub_cancel_right]; simp only [LinearMap.proj_apply]; abel
lemma pairTrace (p r:P) (x: Toe): (∑ a:Axis,∑ b:Axis, (dot3 p r * dotI a b) • D a (η b x)) = traceLag p r x:=by
  unfold traceLag Trace.lamp; rw [LinearMap.sum_apply, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; simp_rw [dot_at,mul_ite,mul_zero,mul_one,ite_smul,zero_smul, Finset.sum_ite_eq]; simp only [Finset.mem_univ,↓reduceIte]; rw [down_eq]; rfl
lemma shell_tangent (t:P)(σ:Bool): (∑ a:Axis, ∑ b:Axis,q σ t a b • D a (η b Sail.cover))∈ Surface 4:=by
  let f a b:= q σ t a b • D a (η b Sail.cover); set A := ∑ a:Axis,∑ b:Axis,f a b; have he : (2:ℝ) • A = ∑ a:Axis,∑ b:Axis,q σ t a b • (D a (η b Sail.cover)-D b (η a Sail.cover)):=by
    unfold A; rw [two_smul]; conv_lhs=> arg 2; rw [Finset.sum_comm]; skip
    simp_rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold f; rw [chosen_sqrt2 σ t i j]; simp [smul_sub, sub_eq_add_neg]
  change A∈ _; rw [← inv_smul_smul₀ (x:=A) (show (2:ℝ)≠0 from two_ne_zero), he]; apply Submodule.smul_mem; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (derivative_forth hill2 i j)
lemma salt (σ:Bool)(p r:P): magnetic σ σ p r-traceLag p r Sail.cover∈ Surface 4:=by
  rw [magnetism]; simp_rw [folding σ p r,add_smul, Finset.sum_add_distrib,pairTrace, add_sub_cancel_left]; -- turn ∑
  simp_rw [Finset.mul_sum,Finset.sum_smul, ← smul_smul]; simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset Axis)) (t:=(Finset.univ:Finset P)), ← Finset.smul_sum]; exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (shell_tangent i σ))
lemma trace_at (x:Cover)(p r:P): traceLag p r Sail.cover x= if p=r∧ x=0 then 1 else 0:=by
  rw [traceLag,Pi.smul_apply,Trace.poisson,dotC]; simp_rw [ite_and]; split_ifs <;> simp
lemma tip4 (σ τ: Bool)(p r:P): magnetic σ τ p r∈ Terrain 4:= by unfold magnetic drawn; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (crevice _ (bunker τ r) i)
lemma sleeved (g:G.Simple)(S:Survey G H d)(he:2≤d)(σ:Bool)(p r:P): drawn σ p (Mn g S σ r)-traceLag p r Sail.cover∈ Surface 4:=by rw [← sub_add_sub_cancel _ (magnetic σ σ p r) _]; exact Submodule.add_mem _ (drawing _ _ (fun i=> stashed g S σ r he i) σ p) (salt σ p r)
lemma slept (g:G.Simple)(S:Survey G H d)(T:Survey G H e)(he:2≤d)(ht:2≤e)(σ:Bool)(p r:P): surveyed g S σ p (Mn g T σ r)-traceLag p r Sail.cover∈ Surface 4:=by rw [← sub_add_sub_cancel _ (magnetic σ σ p r) _]; exact Submodule.add_mem _ (phrase g S T he ht σ σ p r) (salt σ p r)
end YM.XSpace.Relief
