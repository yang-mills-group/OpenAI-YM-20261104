import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicGramAccount

noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary
open Finset Function Filter
open scoped BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
variable {n:ℕ}{V:Fin n→Type*}{I:Fin n→Type*}{W:Type*}
variable [∀i,AddCommGroup (V i)][∀i,Module ℂ (V i)][∀i,Fintype (I i)]
variable [NormedAddCommGroup W][NormedSpace ℂ W]
def salary (B:∀i,Module.Basis (I i) ℂ (V i))(v:(i:Fin n)→V i):ℝ:=
  ∏i,∑j,‖(B i).repr (v i) j‖
theorem original (D:MultilinearMap ℂ V W)(B:∀i,Module.Basis (I i) ℂ (V i))
    (v:(i:Fin n)→V i)(a:ℝ)(paid:∀j:(i:Fin n)→I i,‖D (fun i=>B i (j i))‖≤a):
    ‖D v‖≤a*salary B v:=by
  have rep: D v=∑j:((i:Fin n)→I i),(∏i,(B i).repr (v i) (j i)) • D (fun i=>B i (j i)):=by
    calc
      _=D (fun i=>∑j,(B i).repr (v i) j • B i j):=by congr 1;funext i;exact ((B i).sum_repr (v i)).symm
      _=∑j:((i:Fin n)→I i),D (fun i=>(B i).repr (v i) (j i) • B i (j i)):=D.map_sum _
      _=_:=by simp only [D.map_smul_univ]
  rw [rep]
  calc
    _≤∑j:((i:Fin n)→I i),‖(∏i,(B i).repr (v i) (j i)) • D (fun i=>B i (j i))‖:=norm_sum_le _ _
    _≤∑j:((i:Fin n)→I i),(∏i,‖(B i).repr (v i) (j i)‖)*a:=by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,norm_prod]
      exact mul_le_mul_of_nonneg_left (paid j) (Finset.prod_nonneg fun _ _=>norm_nonneg _)
    _=a*salary B v:=by
      rw [← Finset.sum_mul,mul_comm]
      congr 1
      unfold salary
      rw [Finset.prod_univ_sum]
      simp
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary
end
