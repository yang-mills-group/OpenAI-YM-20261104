import YM.X.Rank.Approx
/-! Control Gram from the finite exponential test coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Screen
open Function Set Filter MeasureTheory Matrix Metric
open YM.Next.SectorChange.Gaussian YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical Kronecker NNReal
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Walls (I:Type):=I ⊕ I×I
def walls (i:Walls I):PTS I := Sum.elim (fun i=> Pi.single i 1) (fun x=> Pi.single x.1 1 + Pi.single x.2 1) i
def one (I:Type)[Fintype I][DecidableEq I]: Tile I:= fun i=> (1:TileK I) i.1 i.2
lemma fox : (folio (Screen.one I))=1 := rfl
lemma columnCost (x:Tile I)(i:I) : shadow (walls (.inl i)) x = ∑ j,x (j,i)^2:= by
  unfold shadow; apply Finset.sum_congr rfl; intro j _; unfold Matrix.mulVec dotProduct walls; simp only [Sum.elim_inl]; simp
  simp [Pi.single_apply,mul_ite]
lemma panel (x:Tile I)(i k:I): shadow (walls (.inr (i,k))) x= ∑ j,(x (j,i)+x (j,k))^2:= by
  unfold shadow walls; simp only [Sum.elim_inr, mulVec_add,Pi.add_apply]; congr 1; unfold Matrix.mulVec; funext j; unfold dotProduct; simp; simp [Pi.single_apply,mul_ite]
lemma solo (i:I):shadow (walls (.inl i)) (Screen.one I)=1:=by rw [columnCost]; unfold Screen.one; simp [Matrix.one_apply,ite_pow]

abbrev gram (x:Tile I): TileK I:= (folio x).transpose*folio x
def screen (I:Type)[Fintype I][DecidableEq I]:Tile I→ PTS (Walls I) := snapshots walls
lemma gram_facts {x:Tile I}(h:screen I x=screen I (Screen.one I)): gram x=1:=by
   have hq i: shadow (walls i) x=shadow (walls i) (Screen.one I):= by
     have he:=Real.exp_injective (congr_fun h i); change -shadow _ _/2=-shadow _ _/2 at he; linarith only [he]
   have hi (i j:I)(v:Tile I): shadow (walls (.inr (i,j))) v= shadow (walls (.inl i)) v+shadow (walls (.inl j)) v+ 2* (gram v i j):= by
     rw [columnCost,columnCost,panel]; unfold gram; simp only [Matrix.mul_apply,transpose_apply,folio,Matrix.of_apply, Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _=> by ring
   rw [show (1:TileK I) = gram (Screen.one I) by unfold gram; rw [fox,transpose_one,mul_one]]
   ext i j; linarith only [hi i j x,hi i j (Screen.one I),hq (.inl i),hq (.inl j),hq (.inr (i,j))]
lemma collar (I:Type)[Fintype I][DecidableEq I]: ∃ δ:ℝ,0<δ∧ IsCompact (screen I ⁻¹' closedBall (screen I (Screen.one I)) δ):= by
   let t : ℝ:=Real.exp (-2:ℝ); let p:=Real.exp (-1/2:ℝ); let δ:=p-t; have hp:0<δ:= sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num)); let K:= closedBall (screen I (Screen.one I)) δ
   refine ⟨δ,hp,(isCompact_closedBall (0:Tile I) 2).of_isClosed_subset (isClosed_closedBall.preimage (snaps (walls (I:=I)))) ?_⟩
   intro x hx; refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg zero_le_two).2 (fun i=>?_))
   rcases i with ⟨i,j⟩
   have ht: ‖screen I (Screen.one I)-screen I x‖ ≤ δ:= by rw [← dist_eq_norm,dist_comm]; exact mem_closedBall.mp hx
   have hD:p-stamp (walls (.inl j)) x≤δ := (le_abs_self _).trans (by
      have he:= (norm_le_pi_norm (screen I (Screen.one I)-screen I x) (.inl j)).trans ht
      change |Real.exp _-stamp (walls (.inl j)) x| ≤ _ at he; rw [solo] at he; exact he )
   have hT : t ≤ Real.exp (-shadow (walls (.inl j)) x / 2):= by unfold δ at hD; change t≤ stamp _ x; linarith only [hD]
   have hS:= Real.exp_le_exp.mp hT; rw [columnCost] at hS
   have hz:= Finset.single_le_sum (s:=Finset.univ) (f:=fun i=> x (i,j)^2) (fun k _=>sq_nonneg _) (Finset.mem_univ i)
   rw [Real.norm_eq_abs]; nlinarith only [hS,hz, sq_abs (x (i,j)),abs_nonneg (x (i,j))]
end YM.PositionX.Rank.Screen
