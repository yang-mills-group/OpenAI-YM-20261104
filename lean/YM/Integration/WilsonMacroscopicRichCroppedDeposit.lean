import YM.Integration.WilsonMacroscopicRichCroppedSeries
import YM.Integration.WilsonMacroscopicRichMeasuredProbe

/-! A genuine cap at the reporting stop places the complete physical nonlinear output projection on a finite set of bonds. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCroppedDeposit
open Function Filter Set Lattice Wilson RG Source Labels Analysis Next.Foundations Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE Spec
open WilsonMacroscopicRichCroppedProbe WilsonMacroscopicRichProbeShell
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (R:Run G)

def window (N p b h L:ℕ) : Finset (Edge (Site (R.family.side b p))) :=
  bonds (R.family.path.rep N p b).p 0 L ∪ ((R.family.localSection h).footprint 0 ×ˢ Finset.univ)

private lemma smooth {n:Side} {f:Config G n→ℂ} {h:ℕ} (s:HasOrderAt f 1 h)
    (a:Finset (Edge (Site n))) (H:Hol G) (o:Site n) (j:Jet G) :
    ContDiffAt ℝ (h:ℕ∞) (f ∘ fields a H h o j) 0 := by
  let z:=mask a ∘ testLog H h o j
  have hz : z 0=0 := by dsimp [z];rw [testLog_zero,map_zero]
  change ContDiffAt ℝ (h:ℕ∞) ((f ∘ increment 1) ∘ z) 0
  exact (show ContDiffAt ℝ (h:ℕ∞) (f ∘ increment 1) (z 0) by rw [hz];exact s).comp 0
    (((mask (G:=G) a).contDiff.contDiffAt.comp 0 (testLog_diff H h o j)).of_le le_top)

/-- The actual complete positive conditional, on the file used in the original terminal account. -/
theorem measured (h:ℕ) (t:Probe G h) : ∃ C:ℝ,0≤C ∧
    ∀ (N p b:ℕ) (T:Slices R.family.path.levels p) (live:b<N) (_:R.family.ref h≤b)
      (Y:Config G (R.family.side N p)→ℂ) (_:Continuous Y) (_:GaugeInvariant Y)
      (q:store R.family h p b) (z:ℝ) (_:reads h N p b q z)
      (_:credit R.family N p h Y b live.le=value (C:=R.family) h N p b q) (L:ℕ),
      let P:=R.family.path.rep N p b
      let y:=WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y
      ‖Germ.jet R.family.params t P.p.threshold 0 y -
        iteratedDeriv t.2.val (y ∘ fields (window R N p b h L) R.family.params h 0 (P.p.threshold • t.1)) 0‖ ≤
        C*Real.exp (-(P.p.supportExponent*L))*z := by
  have kt : t.2.val≤h := Nat.le_of_lt_succ t.2.isLt
  obtain ⟨C,Cp,paid⟩ := series R.family.params t.1 h t.2.val kt
  refine ⟨C,Cp,?_⟩
  intro N p b T live stage Y ct gi q z earns account L P y
  let F:=R.family.labels.level h
  let B:=R.family.localSection h
  let H:=R.family.params
  let θ:=P.p.threshold
  let A:=window R N p b h L
  let core:=B.places (F.scaled θ⁻¹ q.x) (0:Site (R.family.side b p))
  obtain ⟨formed,bill⟩ := earns
  have read := ActualWilsonPrimaryPreparation.original R h N p b stage live.le
  have reg := WilsonMacroscopicRichLastResponse.regular R T live h Y ct gi
  have coreReg := (presented_good 0 read q.x).1
  have sy : HasOrderAt y 1 h := HasOrderAt.fewer read.order (reg.smooth _ (one_healthy _ _ P.p.threshold_pos.le))
  have sc : HasOrderAt core 1 h := HasOrderAt.fewer read.order (coreReg.smooth _ (one_healthy _ _ P.p.threshold_pos.le))
  have visible : (y-core) =ᶠ[𝓝 (1:Config G (R.family.side b p))] fun U=>∑' i,q.regular i U := by
    filter_upwards [offFlags P.p.threshold P.p.threshold_pos] with U quiet
    have acct := congrFun account U
    have complete := WilsonMacroscopicRichReportedPosterior.density R T live.le h Y U
    have eq : q.density 0 B P U = (P.eval U:ℂ)*y U := acct.symm.trans complete
    rw [noFlagCharge q 0 B (R.makes.sections h) quiet] at eq
    have seen : core U+∑' i,q.regular i U=y U := mul_left_cancel₀ (noFlagEval quiet) eq
    change y U-core U=∑' i,q.regular i U;rw [←seen];abel
  have kept := bill
  obtain ⟨_,_,_,_,_,_,⟨e,ce,he⟩,_⟩ := bill
  have se : Summable e := ce.2.1.of_nonneg_of_le (fun i=>(he i).1) (fun i=>P.p.loMass _ _ (he i).1)
  have base := jet_sum (P:=P.p) formed.smooth he se visible h (sy.sub sc) read.order H (θ•t.1) t.2.val kt
  have cl := WilsonMacroscopicRichCroppedSeries.submitted (P:=P.p) formed.smooth he se visible h (sy.sub sc) read.order H (θ•t.1) t.2.val kt A
  have earned := (paid F (R.family.side b p) 0 P q L A Finset.subset_union_left read.order read.power formed kept).2
  have coreLocal := agree (B.placed_local 0 (F.scaled θ⁻¹ q.x)) A
    (fun e e₁ _=>Finset.mem_union_right _ (Finset.mem_product.mpr ⟨e₁,Finset.mem_univ _⟩)) H h 0 (θ•t.1)
  have row := (base.sub cl).tsum_eq
  let global:=H.testLinks h (0:Site (R.family.side b p)) (θ•t.1)
  let cut:=fields A H h (0:Site (R.family.side b p)) (θ•t.1)
  have full_sub : iteratedDeriv t.2.val ((y-core) ∘ global) 0 = iteratedDeriv t.2.val (y ∘ global) 0-iteratedDeriv t.2.val (core ∘ global) 0 :=
    iteratedDeriv_fun_sub (((Germ.computed H reg 0 read.order) _).1.of_le (Nat.cast_le.mpr kt))
      (((Germ.computed H coreReg 0 read.order) _).1.of_le (Nat.cast_le.mpr kt))
  have cut_sub : iteratedDeriv t.2.val ((y-core) ∘ cut) 0 = iteratedDeriv t.2.val (y ∘ cut) 0-iteratedDeriv t.2.val (core ∘ cut) 0 :=
    iteratedDeriv_fun_sub ((smooth sy A H 0 _).of_le (Nat.cast_le.mpr kt)) ((smooth sc A H 0 _).of_le (Nat.cast_le.mpr kt))
  change ‖iteratedDeriv t.2.val (y ∘ global) 0-iteratedDeriv t.2.val (y ∘ cut) 0‖≤_
  have core_eq : iteratedDeriv t.2.val (core ∘ cut) 0=iteratedDeriv t.2.val (core ∘ global) 0 := coreLocal.iteratedDeriv_eq t.2.val
  calc _ = ‖iteratedDeriv t.2.val ((y-core) ∘ global) 0-iteratedDeriv t.2.val ((y-core) ∘ cut) 0‖ := by rw [full_sub,cut_sub,core_eq];abel_nf
       _ ≤ _ := row ▸ earned

end YM.Integration.WilsonMacroscopicRichCroppedDeposit
