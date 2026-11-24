import YM.Integration.WilsonPositionProgramUniformNoise
import YM.Integration.WilsonPositionProgramMeasuredFieldShift

/-! The matrix, affine mean and free-site count on the true chronological forest, before both physical regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramUniformGaussianCalendar
open Function Filter Finset Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open Work.F08 Stationary Tree FormalBulk08 Flat Reef FormalBulk08.Bank FormalBulk08.Jets
open WilsonCoeffUV PhysicalNext.Repeat.Legato Comparison.RG02 RegulatorIR
open scoped Topology BigOperators Matrix Classical
variable {G:Gauge}

private theorem drift (R:Run G)(i:ℕ):
    let V:=R.family.path.levels
    let L:=routes (V.clock.op i 0).patch
    ∃ b:ℝ,1≤b ∧ ∀N:ℕ,let P:=destination V N i
      ∀(c:Side) x y,|Reef.pMean G V.clock.kernel P c (Reef.floor V.clock.kernel P L c) x y|≤b:=by
  intro V L
  let K:=V.clock.kernel
  obtain ⟨s,B,hs,hB,provided,_⟩:=Flat.transports G K.penalty K.penalty_pos
    (V.clock.adm (i+1)) (V.clock.adm i)
  let a:=B/((V.clock.op i 0).patch.L.val:ℝ)
  have ha:0≤a:=by dsimp [a];positivity
  obtain ⟨C,_,renew⟩:=Lodge.bothPay G K L s hs
  refine ⟨max 1 (C*a),le_max_left ..,?_⟩
  intro N P c x y
  have issued:(Flight.duo K.penalty P).A0.strip s a:=by
    change (Flight.duo K.penalty P).A0.strip s (B/(P.L.val:ℝ))
    simpa only [advanceC,List.length_nil,add_zero,pow_one] using (provided P [] (Nat.zero_le _)).1
  have paid:=(renew _ a ha issued).1
  let S:=Flat.primary P.patch K c
  let px:=Bank.saddleP G S L (Sum.inl x)
  let py:=Bank.saddleP G S L (Sum.inr y)
  have named:(Bank.zealand K P L G).acts c px py=Reef.pMean G K P c (Reef.floor K P L c) x y:=
    Bank.twig P L c s a hs ha issued (Sum.inl x) (Sum.inr y)
  rw [←named]
  exact WilsonMarkedInheritedGaussianKernel.folded _ hs.le (Bank.zealandPay K P L paid) c px py

private theorem carry {j t:ℕ}{c f:Side}(S:StepData c f)(P:Flight j t)(K:KernelChoices)
    (hp:S.patch=P.patch)(hk:S.kernel=K)(row:PoleRows S.patch)(hr:HEq row (P.duo K.penalty).A0)
    (b σ:ℝ)
    (mean:∀x y,|Reef.pMean G K P c (Reef.floor K P (routes P.patch) c) x y|≤b)
    (cov:∀x y,|(Flat.testPrecision G (Flat.primary P.patch K c)
      ((routes P.patch).forest (S:=Flat.primary P.patch K c)) P.wing)⁻¹ x y|≤σ):
    let F:=Halo.bios S
    (∀x y,|Flat.rawMean G S F (Bloch.installed S.ratio row) x y|≤b) ∧
    (∀x y,|(Flat.testPrecision G S F P.wing)⁻¹ x y|≤σ):=by
  rcases S with ⟨p,k,size⟩
  change p=P.patch at hp
  change k=K at hk
  subst p
  subst k
  have f':f=c*P.patch.L:=Subtype.ext size
  subst f
  obtain rfl:=eq_of_heq hr
  dsimp only
  rw [WilsonPositionProgramForestRoutes.original]
  exact ⟨mean,cov⟩

theorem original (R:Run G)(i:ℕ):
    let V:=R.family.path.levels
    let cell:=(V.clock.op i 0).patch
    ∃ b σ:ℝ,1≤b ∧ 1≤σ ∧ ∀(N per:ℕ)(hi:i<N),
      let S:=V.clock.op i per
      let F:=Halo.bios S
      let K:=((RunFormalChain.fromRun R).step N i per hi)
      (∀x y,|WilsonMarkedRelativeGaussianBudget.mean R N i per F x y|≤b) ∧
      (∀tag:S.Choices,∀x y,|K.covariance F tag x y|≤σ) ∧
      (∀ _tag:S.Choices,∀x:fieldDir G (R.family.side i per) 1,∀z:(F.Free × G.ColorIndex)→ℝ,
        1+‖(Bulk.translated K F x z).2‖≤WilsonPositionProgramMeasuredFieldShift.height G
        (R.family.side i per) b ‖x‖*(1+‖z‖)) ∧
      Fintype.card (F.Free × G.ColorIndex)=(R.family.side i per).val^4*Fintype.card (Lodge.selected G cell (routes cell)):=by
  intro V cell
  obtain ⟨b,hb,mean⟩:=drift R i
  obtain ⟨σ,hσ,cov⟩:=WilsonPositionProgramUniformNoise.original cell (routes cell) (V.blocks i 0).branches
  refine ⟨b,σ,hb,hσ,?_⟩
  intro N per hi S F K
  let P:=destination V N i
  have hh:=carry S P V.clock.kernel rfl rfl (P.duo V.clock.kernel.penalty).A0 HEq.rfl b σ
    (mean N (R.family.side i per)) (cov P.wing (R.family.side i per))
  have row:∀v w,|WilsonMarkedRelativeGaussianBudget.mean R N i per F v w|≤b:=hh.1
  refine ⟨row,?_,fun tag x z=>WilsonPositionProgramMeasuredFieldShift.draw R N i per hi F tag b (zero_le_one.trans hb) row x z,?_⟩
  · intro tag v w
    have eq:=congrFun (congrFun (WilsonMovingRunWickCoordinates.precision R N i per hi F tag)
      ((Reef.pines F) v)) ((Reef.pines F) w)
    simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply] at eq
    change |(((RunFormalChain.fromRun R).step N i per hi).covariance F tag) v w|≤σ
    rw [eq]
    exact hh.2 _ _
  · obtain ⟨_,_,_,_,old⟩:=WilsonPositionProgramChronologicalGaussian.original R (i+1) i (Nat.lt_succ_self _)
    exact (old per).2.2

end YM.Integration.WilsonPositionProgramUniformGaussianCalendar
end
