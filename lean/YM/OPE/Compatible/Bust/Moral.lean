import YM.OPE.Compatible.Bust.Doze
/-!
# Star algebra. at ordinary/H
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
-- Cot via act
abbrev OrderR (G:Gauge)(N:Side): Matrix (Tab (Shade G) N) (FreeResolvent.Slot G N 1) ℝ:= (1: Mat (FreeResolvent.Slot G N 1)).submatrix (station G N) id
lemma volx (G:Gauge)(N:Side)(x:Vec G N 1): OrderR G N*ᵥ x=deckW G N x:=by funext i; unfold Matrix.mulVec dotProduct OrderR; simp only [Matrix.submatrix_apply,id_eq, Matrix.one_apply,ite_mul,one_mul,zero_mul]; rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)];rfl
lemma virtua (G:Gauge)(N:Side)(x:deck (Shade G) N): (OrderR G N)ᵀ*ᵥ x=(deckW G N).symm x:=by
     funext i; obtain ⟨i,rfl⟩:= (station G N).surjective i; unfold Matrix.mulVec dotProduct; simp only [Matrix.transpose_apply,OrderR,Matrix.submatrix_apply,id_eq,Matrix.one_apply,Equiv.apply_eq_iff_eq,ite_mul,one_mul,zero_mul, Finset.sum_ite_eq',Finset.mem_univ,if_true]; exact congr_fun ((deckW G N).apply_symm_apply x).symm i
lemma spotON (v:Train r)(n:Side)(G:Gauge): Cot L G v n= OrderR G n*PhV L v G n* (OrderR G n)ᵀ:=by
    ext i j; simp only [Matrix.mul_apply,OrderR,Matrix.transpose_apply,Matrix.submatrix_apply,id_eq,Matrix.one_apply,ite_mul,mul_ite,one_mul,zero_mul,sum_ite_eq,mem_univ,if_true,mul_one,mul_zero]; rfl
abbrev formSong (m k:ℕ)(G:Gauge)(p:Site N) : Seat k m (Shade G)→ₗ[ℝ] Song (Vec G N 1):= pulling (OrderR G N) ∘ₗ worldR m k p _
lemma tensors (p: Seat k m (Shade G))(i:ℕ)(x:Site N)(y: Fin i→ Vec G N 1): formSong m k G x p i y=scribe x (lilies m k _ p i) (deckW G N ∘ y):=by
     change worldR m k x (Shade G) p i (fun j=>OrderR G _*ᵥ y j)= _; simp_rw [volx]; rw [show (worldR m k x (Shade G) p) i=orchestra (lilies m k _ p i) x from toScript m i x _]; exact (instruments _ (tiller m (moduleAt m k i _ p)) x ((deckW G N) ∘ y)).tsum_eq.symm
lemma formulaS (p: Seat k m (Shade G))(v:Train r)(h:r≥4)(x:Site N)(i:ℕ): formSong m k G x (lapD (pointAt G v h L N) m k p) i= opus (PhV L v G N) (formSong m k G x p) i:=by
     change ((worldR m k x _ (lapD _ _ _ p) i).compContinuousLinearMap (fun _=>_))= wind i • Semester (PhV L _ _ N) ((worldR m k x _ p (i+2)).compContinuousLinearMap fun _=>_); rw [hornT _ _ _ (formsC v h x) p i,columnAlong _ _ _ (spotON (L:=L) v N G)]; rfl
lemma reserves (p:Seat k (m+1) (Shade G))(v:Train r)(h:4≤r)(q:ℕ)(x:Site N)(he: abides (lilies (m+1) k _ p q)): Reserve (Prog L v G N) (formSong (m+1) k G x p q):=by
     intro i u y hh; let b:=lilies (m+1) k (Shade G) p q; rw [tensors]; rw [show deckW G N ∘ update u i y=update (deckW G N∘ u) i (deckW G N y) from ?_]; exact HaQ he h m (humor (m:=m+1) (moduleAt (m+1) k q _ p)) x y hh _ i -- underscores
     funext j; by_cases hp:j=i<;>simp [hp]
lemma finHeat (p: Seat k m (Shade G))(v:Train r)(h:r≥4)(x:Site N)(i:ℕ)(u:ℝ): formSong m k G x (fixExp (lapD (pointAt G v h L N) m k).toLinearMap u i p)= fixExp (opus (PhV L v G N)) u i (formSong m k G x p):=by
     let T:= pointAt G v h L N; let f:= (lapD T m k).toLinearMap; let E:=formSong m k G x; let D:= opus (PhV L v G N); have he(i:ℕ): E ((f^i) p)=(D^i) (E p):=by induction i with | zero=>rfl| succ i ih=> rw [pow_succ',pow_succ',End.mul_apply,End.mul_apply,← ih]; exact funext fun i=> formulaS _ _ _ _ i
     rw [Hflow,Hflow,map_sum]; exact sum_congr rfl fun i _=>by rw [map_smul,he i]
lemma strikesT (p: Seat k m (Shade G))(x: Site N)(v: Bid.Dir G N): Strike k (formSong m k G x p) (flats G N v)= Flair (lilies m k _ p) k (spool G N v) x:=by
    unfold Strike Tensor.diagonal Flair; refine sum_congr rfl ?_; intro i _; rw [tensors]; unfold Script.value; congr 1; funext j; exact ((deckW G N).apply_symm_apply _)
end YM.OPE.Silt.Float
