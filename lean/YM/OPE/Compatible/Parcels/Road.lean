import YM.OPE.Compatible.Parcels.Sack
/-! Pump and sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology Classical BigOperators
variable {I J K:Type*}
variable {X:Type*}[NormedAddCommGroup X]{Y:Type*}[NormedAddCommGroup Y]
namespace Sack
variable {p q:J→I→X} {A B:ℝ} {i:I} {u:I→ℝ} {a:J→ℝ}
lemma barrel (h:∀ j,Sack u (p j) (a j))(ha: SumBudget a A): Sack (fun j:J×I=>u j.2) (Function.uncurry p) A:=by
   let g (j:J×I):= u j.2*‖p j.1 j.2‖; have hz: 0≤g:= fun i=> (h i.1).1 i.2; let q j:= ∑' i:I,g (j,i)
   have he: q ≤ a:= fun i=> (h i).2.2; have hp:Summable q:= ha.2.1.of_nonneg_of_le (fun i=>tsum_nonneg (fun j=>hz (i,j))) he
   have hh:Summable g:= (summable_prod_of_nonneg (f:=g) hz).2 ⟨fun i=>(h i).2.1,hp⟩; exact ⟨hz,hh,(hh.tsum_prod).trans_le ((hp.tsum_le_tsum he ha.2.1).trans ha.2.2)⟩
lemma collectible (h:Sack (fun i:J×I=> u i.2) (Function.uncurry p) A) (hp:1 ≤ u)(i:I): Summable fun j=> ‖p j i‖:=by
   have ht:= h.mass (fun i=> show 1 ≤ u i.2 from hp i.2); exact ht.2.1.prod_symm.prod_factor i
lemma draw [CompleteSpace X](h:Sack (fun i:J×I=> u i.2) (Function.uncurry p) A)(hp:1 ≤ u):Sack u (fun i=> ∑' j,p j i) A:=by
   let g (i:J×I):= u i.2*‖p i.1 i.2‖; have he : Summable g:= h.2.1; let c(i:I):= ∑' j:J,g (j,i)
   have hc:0 ≤ c:=fun i=>tsum_nonneg fun j=> h.1 (j,i); have hv : Summable c:= (summable_prod_of_nonneg (f:= g ∘ Prod.swap) (fun i=>h.1 i.swap)|>.1 he.prod_symm).2
   have hg : ∑' i,c i=∑' i,g i:= he.tsum_comm.trans he.tsum_prod.symm
   have hh : (fun i:I=>0) ≤ u:= fun i=> zero_le_one.trans (hp i)
   apply Work.F08.budget_minor (show SumBudget c A from ⟨hc,hv,hg.trans_le h.2.2⟩) (fun i=>mul_nonneg (hh i) (norm_nonneg _)); intro i; exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (h.collectible hp i)) (hh i)).trans_eq (tsum_mul_left).symm
lemma draws [CompleteSpace X](h:∀ j,Sack u (p j) (a j))(ha: SumBudget a A)(hp:1 ≤ u): Sack u (fun i=>∑' j,p j i) A:= (barrel h ha).draw hp
section move
variable {z:J→ℝ}{φ:J→ℝ}{T:J→I→X}
-- weight ℓ majorization
lemma carried [NormedSpace ℝ X](h:Sack φ z A)(hp:∀ i,Sack u (T i) (φ i*B))(hx:0 ≤ B): Sack (fun i:J×I=>u i.2) (uncurry fun j=> z j • T j) (A*B):=by
   apply barrel (fun i=> show Sack u _ (φ i*‖z i‖*B) from ((hp i).scale_line _).tips (by apply le_of_eq; ring)); refine ⟨fun i=> mul_nonneg (h.1 i) hx,h.2.1.mul_right B,?_⟩; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 hx
-- Fubini for sums
lemma skews [CompleteSpace X]{p:J→ℕ→X}{x:J×ℕ→ℝ}(h:Sack x (uncurry p) A)(hx:1 ≤ x): ∑' i,∑' j,p i j=∑' j,∑' i,p i j:= (h.water hx).tsum_comm.symm
end move
end Sack
end YM.OPE.Flume
