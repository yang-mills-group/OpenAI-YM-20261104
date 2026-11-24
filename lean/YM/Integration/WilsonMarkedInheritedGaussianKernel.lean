import YM.FormalBulk08.Bank.Sandy

/-! Bounds on the actual affine shift and fluctuation covariance of a filed
forest. Each bound precedes all finite torus sizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedInheritedGaussianKernel
open Function Filter Finset Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open Work.F08 Stationary Tree FormalBulk08 Flat Reef FormalBulk08.Bank FormalBulk08.Jets
open scoped Topology BigOperators Matrix Classical

theorem folded {I J:Type*} (A:Bloch.Row I J) {σ b:ℝ} (hσ:0≤σ) (paid:A.strip σ b)
    (n:Side) (x:Site n×I) (y:Site n×J) : |A.acts n x y|≤b := by
  let f (t:Cover):=if y.1=x.1+wrap n t then A x.2 y.2 t else 0
  have spent:=(paid x.2 y.2).unweighted hσ
  have h (t:Cover) : ‖f t‖≤‖A x.2 y.2 t‖ := by
    by_cases same:y.1=x.1+wrap n t <;> simp [f,same]
  have sm:=spent.2.1.of_nonneg_of_le (fun t=>norm_nonneg (f t)) h
  change |∑' t,f t|≤b
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm sm).trans ((sm.tsum_le_tsum h spent.2.1).trans spent.2.2)

variable {G:Gauge} {K:KernelChoices} {j t:ℕ} (P:Flight j t) (L:Lodge P.patch)
    (h:P.patch.Branches K G)

theorem covariance :
    ∃b:ℝ, 1≤b ∧ ∀n:Side,
      ((Reef.ferry P h L n).saddle.q).PosDef ∧ ∀x y, |(Reef.ferry P h L n).saddle.q x y|≤b := by
  obtain ⟨σ,c,hσ,paid⟩:=(Flat.gamma_ready G K P L h).1
  refine ⟨max 1 c,le_max_left ..,fun n=>?_⟩
  obtain ⟨positive,product⟩:=Reef.honey P h L n
  have he:=Matrix.inv_eq_right_inv product
  refine ⟨?_,fun x y=>?_⟩
  · change (Reef.puppet P h L n).PosDef
    rw [←he]
    exact positive.inv
  · let s:=L.splitting (G:=G) (S:=Flat.primary P.patch K n)
    change |(Flat.gamma G K P L h).acts n (s x) (s y)|≤max 1 c
    exact (folded (Flat.gamma G K P L h) hσ.le paid n (s x) (s y)).trans (le_max_right ..)

theorem drift (G:Gauge) (K:KernelChoices) (hj:4≤j) (ht:4≤t) :
    ∃b:ℝ,1≤b ∧ ∀(n:Side) x y,|Reef.pMean G K P n (Reef.floor K P L n) x y|≤b := by
  obtain ⟨σ,B,hσ,hB,provided,_⟩:=Flat.transports G K.penalty K.penalty_pos hj ht
  let a:=B/(P.L.val:ℝ)
  have ha:0≤a:=by dsimp [a]; positivity
  have issued:(Flight.duo K.penalty P).A0.strip σ a:=by
    simpa only [advanceC,List.length_nil,add_zero,pow_one,a] using (provided P [] (Nat.zero_le _)).1
  obtain ⟨C,_,renew⟩:=Lodge.bothPay G K L σ hσ
  have paid:=(renew _ a ha issued).1
  refine ⟨max 1 (C*a), le_max_left .., fun n x y=>?_⟩
  let S:=Flat.primary P.patch K n
  let px:=Bank.saddleP G S L (Sum.inl x)
  let py:=Bank.saddleP G S L (Sum.inr y)
  have named: (Bank.zealand K P L G).acts n px py=Reef.pMean G K P n (Reef.floor K P L n) x y:=
    Bank.twig P L n σ a hσ ha issued (Sum.inl x) (Sum.inr y)
  rw [←named]
  exact folded _ hσ.le (Bank.zealandPay K P L paid) n px py

end YM.Integration.WilsonMarkedInheritedGaussianKernel
end
