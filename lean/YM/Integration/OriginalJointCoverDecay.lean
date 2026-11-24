import YM.Integration.OriginalMarkedWindingAllRoots
import YM.Integration.FundedMarkedPathSelection

/-! A strongly purchased native pre-block joint tensor controls every
physical torus output tensor with its full marked and field diameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalJointCoverDecay
open Function Finset Lattice Wilson RG FreeResolvent Gauge Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider OriginalPhysicalWindingRows
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue
open scoped BigOperators Classical

variable {V α E : Type} [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : Side} {l : ℕ}
    (J : Finset V) (y : V → Cover)

def diameterAt (p : J → Site n) (z : dock (Site n) α l) :=
  diameter (univ.image p ∪ univ.image fun i => (z i).1)

omit [DecidableEq V] [Fintype V] [DecidableEq α] [Fintype α] in
theorem wrapped (p : J → Site n) (hp : ∀ i : J,wrap n (y i)=p i)
    (z : dock (Site n) α l) (t : dock Cover α l) (ht : slideC n t=z) :
    diameterAt J p z ≤ Syn terrain y J t := by
  let U := univ.image p ∪ univ.image fun i => (z i).1
  let tags := foyer y J t
  have observed (v : Site n) (h : v∈U) : ∃ i : J⊕Fin l,wrap n (tags i)=v := by
    rcases mem_union.mp h with h | h
    · obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact ⟨Sum.inl i,(hp i).trans hi⟩
    · obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact ⟨Sum.inr i,(congrArg Prod.fst (congrFun ht i)).trans hi⟩
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  obtain ⟨i,hi⟩ := observed a ha
  obtain ⟨j,hj⟩ := observed b hb
  rw [←hi,←hj]
  exact (wrapGap (tags i) (tags j)).trans (leg_le terrain tags i j)

omit [DecidableEq V] [Fintype V] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Before the physical block a single Riesz-valued tensor has an actual
strong `Wig` bill. After periodization, all source and field directions
remain inside the same exponential diameter. -/
theorem periodized (p : J → Site n) (hp : ∀ i : J,wrap n (y i)=p i)
    (o : J) (F : Ten E (Cloth α) l) {s A : ℝ} (hs : 0<s) (paid : Wig terrain y s A J F)
    (z : dock (Site n) α l) :
    ‖Carp.plume F n z‖ ≤ A*tiePay α l (s/4)*Real.exp (-(s/2)*(diameterAt J p z:ℝ)) := by
  let d := (diameterAt J p z:ℝ)
  let T : Ten E (Cloth α) l := fun t => if slideC n t=z then F t else 0
  let price := A*Real.exp (-(s/2)*d)
  have pos : 0 ≤ price := mul_nonneg paid.1 (Real.exp_pos _).le
  have cut : Wig terrain y (s/2) price J T := by
    refine ⟨pos,?_⟩
    intro t
    by_cases h : slideC n t=z
    · rw [show T t=F t from if_pos h]
      apply (paid.2 t).trans
      dsimp only [price]
      rw [mul_assoc,←Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ paid.1
      apply Real.exp_monotone
      have hd : d ≤ (Syn terrain y J t:ℝ) := by
        dsimp only [d]
        exact_mod_cast wrapped J y p hp z t h
      nlinarith only [mul_le_mul_of_nonneg_left hd hs.le]
    · simp only [T,h,if_false,norm_zero]
      exact mul_nonneg pos (Real.exp_pos _).le
  have width := cut.to_cork (show 0 ≤ s/2 by positivity) o.property
  have real := clothBound width (t:=s/4) (by positivity) (by linarith) z
  have identical : Carp.plume F n z=Carp.plume T n z := by
    unfold Carp.plume
    apply tsum_congr
    intro t
    by_cases h : slideC n t=z <;> simp [peglet,T,h]
  rw [identical]
  refine (norm_tsum_le_tsum_norm real.2.1).trans (real.2.2.trans ?_)
  have discount : Real.exp (-(s/4)*(tread (tor n) (wrap n (y o)) z:ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
  have nonnegative : 0 ≤ tiePay α l (s/4) := by
    unfold tiePay
    by_cases h0 : l=0
    · simp [h0]
    · exact pow_nonneg (boardPay_nn (by positivity)) _
  rw [show s/2-s/4=s/4 by ring]
  exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right pos discount) nonnegative).trans_eq
    (by dsimp [price,d]; ring)

variable {G : Gauge} {D : V → ℕ} {k : V → ℕ} {e m N : ℕ} {A : ℝ}
    {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}

theorem output (X : FundedMarkedPathSelection.Input Q hm univ k D A) (ha : 0 ≤ A) (hN : m<N)
    (closed : Cloze D k Q Credit.leanC) (p : J → Site n) (hp : ∀i:J,wrap n (y i)=p i)
    (o : J) {i : ℕ} (hi : i ≤ e) (z : Fin l → PhysicalWilsonRootedHessian.Label G n) :
    let F := (FundedMarkedPathSelection.output X J N y).2 i l
    let s := Vσ Q m hm
    ‖Carp.plume F n z‖ ≤ FundedMarkedPathSelection.price Q k D A J m*
      tiePay (Exterior.TypeFace 1 × G.ColorIndex) l (s/4)*Real.exp (-(s/2)*(diameterAt J p z:ℝ)) := by
  exact periodized J y p hp o _ (perk hm)
    ((FundedMarkedPathSelection.ready X (subset_univ J) ha hN closed y).2 i
      (Nat.lt_succ_of_le hi) l) z

end YM.Integration.OriginalJointCoverDecay
end
