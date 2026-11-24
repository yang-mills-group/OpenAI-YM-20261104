import YM.Pert.Phases.Delivery
/-!
Prepare common reference lifts giving uniform left inversion through actual and
free test rows, including all characters. This is the detector sequence,
not a statement that every sufficiently deep mesh is a plateau.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Pert.PhaseControl
open Function Filter Topology Set MeasureTheory Analysis Extraction Retain Table Maxwell Cells Bid Org OS
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G} {F:Order} {S:Table C.book} (B:Spec.Final C F S)
variable {d:ℕ} (X:Columns C S d) (Y:X.Trials) (Q:Y.Valid F)

lemma board_injection : Injective (freeBoard (X:=X)) := fun i j he=> X.full (funext fun a=>
   ((freeBoard_sample a _).symm.trans (congr_fun he a)).trans (freeBoard_sample a _))
theorem exact_ranks (v:members B) (j : ℕ) :
    Module.finrank ℂ ((standard C).Field j) = Module.finrank ℂ ((phase B v).Field j):= by
    obtain ⟨H,h⟩:=B.phase.transport.comparator
    have hn:=B.phase.phase.retains v j
    have hi : Module.finrank ℂ (S.Field j) = Module.finrank ℂ ((standard C).Field j) :=
       (h j).choose.finrank_eq
    refine hi.symm.trans ?_
    change (fun s:Submodule ℂ (C.book.Ref j)=>Module.finrank ℂ (C.book.Ref j ⧸ s)) (S.null j) = _
    exact congr_arg (fun s:Submodule ℂ (C.book.Ref j)=>Module.finrank ℂ (C.book.Ref j ⧸ s)) hn.symm

include Q in
lemma test_unit (k : ℕ) (v:members B) : phaseField B Y k v ((standard C).unit d)=(phase B v).unit d := by
   have hu : Y.later k 0 = C.refUnit d := by
      apply Extraction.Order.unique (F) _ _ (Q.responds k 0)
      refine ⟨Eventually.of_forall fun i=> trivial, (fun p=> C.refUnit d), fun p h=> ?_, tendsto_const_nhds⟩
      exact tendsto_const_nhds.congr fun n=>Eq.symm (Q.unit k _ p)
   rw [← X.initial]
   change ((X.basis.constr ℂ _) (X.basis 0)) = _
   rw [Module.Basis.constr_basis,hu]; rfl

include Q in
lemma test_real (k : ℕ) (v:members B) (c : Fin (X.dim+1)) :
      (phase B v).conj (B.phase.phase.states v).spin d (phaseField B Y k v (X.basis c))=phaseField B Y k v (X.basis c) := by
   have hu: star (Y.later k c) = Y.later k c := by
      apply Extraction.Order.unique F _ _ _ (Q.responds k c)
      obtain ⟨hD,p,hT,hP⟩:=Q.responds k c
      refine ⟨hD,fun σ=> star (p σ),fun σ hD=> ?_,hP.star⟩
      exact (hT σ hD).star.congr fun i=>Q.conjugate ..
   change _ = ((X.basis.constr ℂ (fun i=>(phase B v).project d (Y.later k i))) (X.basis c))
   change (phase B v).conj _ _ ((X.basis.constr ℂ _) (X.basis c))=_
   simp_rw [Module.Basis.constr_basis,Table.conj_project,hu]

structure PhasePrice (X : Columns C S d) (Y : X.Trials) : Prop where
   ready : Y.Valid F
   paid {ε:ℝ} (he:0 < ε) : ∀ᶠ k:ℕ in atTop, ∀ v, ‖instruments B Y k v-freeBoard (X:=X)‖ ≤ ε
   unit k v : phaseField B Y k v ((standard C).unit d)=(phase B v).unit d
   real_ (k : ℕ) (v:members B) (c : Fin (X.dim+1)) :
      (phase B v).conj (B.phase.phase.states v).spin d (phaseField B Y k v (X.basis c))=phaseField B Y k v (X.basis c)
   spans : ∀ᶠ k:ℕ in atTop, ∀ v, Bijective (phaseField B Y k v)
   noLoss : ∃ D:ℝ, 0 ≤ D ∧ ∀ᶠ k:ℕ in atTop, ∀ v x, ‖x‖ ≤ D*‖instruments B Y k v x‖

include Q
variable (hf:Funds Y Q B.α.unselected)
include hf
lemma ticket_price : PhasePrice B X Y := by
   let t:=freeBoard (X:=X)
   obtain ⟨a,ha⟩:=LinearMap.exists_leftInverse_of_injective t.toLinearMap (LinearMap.ker_eq_bot_of_injective (board_injection X))
   let A:= a.toContinuousLinearMap
   let D:=max 1 ‖A‖
   have haF (x) : A (t x)=x:= LinearMap.congr_fun ha x
   have hd: ‖A‖ ≤ D := le_max_right ..
   have hd' : 1 ≤ D := le_max_left ..
   have hpos : 0 < 1/(2*D) := by positivity
   obtain ⟨K,hK⟩:=eventually_atTop.mp (board_uniform B Y Q hf hpos)
   let M:=2*D
   suffices h : ∀ k, K ≤ k → ∀ v x, ‖x‖ ≤ M*‖instruments B Y k v x‖ by
      have hp : ∀ᶠ k:ℕ in atTop, ∀ v, Bijective (phaseField B Y k v) :=
        eventually_atTop.mpr ⟨K,fun k hk v=> by
            have he : Injective (phaseField B Y k v) := by
                intro x y he
                have hh:= h k hk v (x-y)
                have h' : phaseField B Y k v (x-y)=0 := by rw [map_sub,he,sub_self]
                change ‖_-_‖ ≤ _ * ‖(LinearMap.pi (probe' (D:=phase B v) Y k)) _‖ at hh
                change ‖_-_‖ ≤ _ * ‖(LinearMap.pi (probe' (D:=phase B v) Y k)) (phaseField _ _ _ _ (x-y))‖ at hh
                rw [h',map_zero,norm_zero,mul_zero] at hh
                exact sub_eq_zero.mp (norm_le_zero_iff.mp hh)
            exact ⟨he,LinearMap.injective_iff_surjective_of_finrank_eq_finrank (exact_ranks B v _) |>.mp he⟩ ⟩
      refine ⟨Q,board_uniform B Y Q hf, test_unit B X Y Q,test_real B X Y Q,hp,⟨M,by positivity,eventually_atTop.mpr ⟨K,h⟩⟩⟩
   intro k hk v x
   have hx:= hK k hk v
   have hA:=A.le_opNorm (freeBoard (X:=X) x)
   have hz:= ((instruments B Y k v)-freeBoard (X:=X)).le_opNorm x
   change ‖instruments B Y k v x-t x‖ ≤ _ at hz
   change ‖A (t x)‖ ≤ _ at hA
   rw [haF x] at hA
   have hp : ‖instruments B Y k v x-t x‖ ≤ 1/(2*D)*‖x‖:=hz.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
   have ht : ‖t x‖ ≤ ‖instruments B Y k v x-t x‖+‖instruments B Y k v x‖ := by
      have ht := norm_add_le (instruments B Y k v x) (-(instruments B Y k v x-t x))
      have hs: instruments B Y k v x - (instruments B Y k v x-t x)=t x:= sub_sub_cancel ..
      rw [add_comm ‖_-_‖ ‖instruments _ _ _ _ x‖]
      simpa only [←sub_eq_add_neg,hs,norm_neg] using ht
   have hy : ‖x‖ ≤ D * (1/(2*D)*‖x‖ + ‖instruments B Y k v x‖) := (hA.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (ht.trans (add_le_add_left hp _)) (zero_le_one.trans hd'))
   field_simp at hy
   change _ ≤ 2*D*_ 
   nlinarith only [hy,hd']

omit Q hf in
/-- Unconditional for *these* sequences of detecting rows per horizon on the
same construction used by `flowEndpoint`. Does not compare arbitrary OPE
probes in any character. -/
theorem every_phase (hM : MergeProof.Ribbons.Materials C) (d:ℕ) :
    ∃ (X : Columns C S d) (Y:X.Trials), PhasePrice B X Y := by
    obtain ⟨X,Y,Q⟩:=B.room.corrected d
    exact ⟨X,Y,ticket_price B X Y Q (fundsSupplied B Y Q hM)⟩
end YM.Pert.PhaseControl
