import YangMills.WilsonProof.NativeSupport.JointRepaint
import YM.RGGapR2.Rough

/-! Convert the original rooted bills of a regular or dirty inherited
sheet into its actual inflated entry tariff, paying the native
root-to-site reserve only on admission. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Finset Function Lattice RG Wilson Marker Packet MergeProof MergeProof.Accent Extra.Multi
open scoped Classical BigOperators
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {G : Gauge} {n : Side}

theorem rooted_input (b μ : ℕ) (e U t A D : ℝ) (uu : 0≤U) (a0 : 0≤A)
    (w : V → ℝ) (hw : ∀ y,0<w y) (fresh : Finset V) (o : V → Site n)
    (occ : Occupancy o μ) (X : I → Support n) (F : I → Config G n → Poly (YM.Stock.census V))
    (borne : ∀ i,Borne o (X i) (F i) t) (mute : ∀ i Z,(F i Z).part (tag ∅)=0)
    (previous : ∀ i S,Menu.Vivid F i (tag S) → Disjoint S fresh)
    (cap : I → Finset V → ℝ) (nonneg : ∀ i S,0≤cap i S)
    (bound : ∀ i Z S,‖(F i Z).part (tag S)‖≤cap i S)
    (roots : ∀ y:V,(∑ i,Real.exp ((e+1)*coverNumber b (X i))*
      ∑ S:Finset V with y∈S,Poly.toll w (tag S)*cap i S)≤U) :
    Towed (weight w A D fresh) X (fun i Z=>repaint (F i Z)) b e
      (A*((μ:ℝ)*siteFactor b*U)) := by
  let live i (S:Finset V) := Menu.Vivid F i (tag S)
  let c i (S:Finset V) := if live i S then cap i S else 0
  have nc i S : 0≤c i S := by unfold c; split; exact nonneg ..; rfl
  have cb i S : c i S≤cap i S := by unfold c; split; rfl; exact nonneg ..
  have value i Z S : ‖(F i Z).part (tag S)‖≤c i S := by
    unfold c; split
    next => exact bound ..
    next no =>
      have z : (F i Z).part (tag S)=0 := not_not.mp fun bad=>no ⟨Z,bad⟩
      rw [z,norm_zero]
  have hot i S (h:live i S) : S.Nonempty := by
    obtain ⟨Z,coef⟩:=h
    exact nonempty_iff_ne_empty.mpr fun eq=>coef (eq ▸ mute i Z)
  let fee (j:I×Finset V) := Poly.toll w (tag j.2)*c j.1 j.2
  have fee0 j : 0≤fee j := mul_nonneg (Poly.worth hw _).le (nc ..)
  let address (j:I×Finset V) := X j.1
  have root : Rooted Prod.snd address b (e+1) fee U := by
    intro y
    refine ⟨fun i=>by dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (fee0 _); rfl,Summable.of_finite,?_⟩
    rw [tsum_fintype,Fintype.sum_prod_type]
    apply le_trans _ (roots y)
    apply sum_le_sum
    intro i _
    rw [sum_filter,mul_sum]
    apply sum_le_sum
    intro S _
    by_cases hold : y∈S
    · simp only [hold,if_true,address,fee]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (cb i S) (Poly.worth hw _).le) (Real.exp_pos _).le
    · simp [hold]
  have pins (j:I×Finset V) (h:0<fee j) : ∃ y∈j.2,o y∈address j := by
    have real : live j.1 j.2 := by
      by_contra no
      simp only [fee,c,no,if_false,mul_zero,lt_self_iff_false] at h
    obtain ⟨y,hit⟩:=hot _ _ real
    obtain ⟨Z,hZ⟩:=real
    exact ⟨y,hit,(borne j.1).place _ Z hZ (mem_image_of_mem o hit)⟩
  have hits := root_hit occ fee0 uu pins root
  let row i := A*∑ S:Finset V,fee (i,S)
  refine ⟨row,Summable.of_finite,?_,?_⟩
  · intro x
    refine ⟨fun i=>by dsimp only; split; exact mul_nonneg (mul_nonneg a0 (sum_nonneg fun _ _=>fee0 _)) (Real.exp_pos _).le; rfl,Summable.of_finite,?_⟩
    rw [tsum_fintype]
    apply le_trans _ (mul_le_mul_of_nonneg_left (Budget.cap (hits x) univ) a0)
    apply le_of_eq
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases seen : x∈X i
    · simp only [address,seen,if_true,row,sum_mul,mul_assoc]
    · simp [address,seen]
  · intro i
    let major (p : (YM.Stock.census (Ink V)).Mode) := ∑ S : Finset V,if p=tag (wear S) then c i S else 0
    refine ⟨major,fun p=>sum_nonneg fun S _=>by split; exact nc ..; rfl,?_,?_⟩
    · intro Z p
      change ‖(repaint (F i Z)).part p‖ ≤ major p
      rw [repaint,Poly.part_sum]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro S _
      rw [Poly.part_send]
      split
      next => exact value i Z S
      rw [norm_zero]
    · change (∑ p,Poly.toll (weight w A D fresh) p*major p)≤_
      simp only [major,mul_sum,mul_ite,mul_zero]
      rw [sum_comm]
      change _ ≤ A*∑ S:Finset V,fee (i,S)
      rw [mul_sum]
      apply sum_le_sum
      intro S _
      rw [sum_ite_eq',if_pos (mem_univ _)]
      by_cases seen : live i S
      · rw [wear_toll w A D fresh S (hot i S seen) (previous i S seen),mul_assoc]
      · simp [fee,c,seen]

end YM.Integration.InletSusceptibility.Painted
