import YM.Integration.WilsonFirstReceivedRadialStencil
import YM.Integration.WilsonFirstReceivedRadialForecast
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogEnrolled

/-! Extend a deposited Taylor polynomial from the original positive-coupling
Wilson probes to the whole independent connected forecast on a larger ray.
The physical polynomial retains its own approximation fee at the real nodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedRadialComparison
open Filter Function Finset Lattice Wilson RG Precision Tree Marker Multi Exterior
open FullQLocal FullQLocal.RenderedStep LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open WilsonMatrixTicketLanesReportedPrepaid WilsonFirstReceivedRadialStencil
open scoped Classical BigOperators Topology
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
local notation "Γ" => Stock.census V

theorem original (R:Run G) (camp:Campaign R) (hG:G.Simple) (paid:Paid G R.kit)
    (u:V→MS.Rake.Label B) (Q:MS.Land.Prescription B) (cap K₀ q:ℕ) (μ:ℝ) {ε:ℝ} (ep:0<ε) :
    ∃n ≥ q,∀ᶠ b:ℕ in atTop,∀(J:Request V),n ≤ J.order → ∀(A:NumericSchedule R.family J)
      (profile:∀k,k ≤ (R.metals.p.profile k).order ∧ k ≤ (R.metals.p.profile k).power)
      (d:LocalFormal.Datum R.family (Γ)),d.level=b→d.cutoff=d.level+1→
      ∀(o:V→Site (R.family.side (d.level+1) d.period)) (ks:V→ℕ),(∀i,ks i ≤ K₀)→
      ∀(hm:ActualOriginalQInitialInput.start R hG u J A profile ≤ d.level)
        (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val),
      ActualOriginalQLayout.referenceLevel R u ≤ d.level+1→
      ∀(t:TestSpace (ActualOriginalQPointSetup.request R u J).tests),
        let S:=R.family.path.levels.clock.op d.level d.period
        let P:=R.family.path.rep d.cutoff d.period (d.level+1)
        let K:=(RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
        let g:=regulatorRun R.family (d.level+1) d.period (d.level+1)
        let X:=((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks).leaf t).density
        let W:=(ActualOriginalQInitialInput.input R hG u J A d Q o μ ks profile hm hp).colors t
        let w:=WilsonPositionSeparatedProfileMayerInitialLogWeights.weight
          (WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t)
        ∀ (F:Forest S.ratio) (tag:S.Choices) (a:fieldDir G (R.family.side d.level d.period) 1),
          (∀i,‖Exterior.collect G a i‖ ≤ (cap:ℝ)+1)→∀ (s:(Stock.census V).Mode) (D:ℕ),
          let actual:=fun j:ℕ=>(Local.cumulant P X S (Integral.sample g (node D j • a))).part s
          let independent:=fun x:ℝ=>(Order.value (g:ℂ) (Order.logMarked
            (Bulk.Fk K F tag W (x • a) n))).part s
          ∀ (physical:Polynomial ℂ) (inputFee:ℝ),
            physical.natDegree≤D → n+2≤D →
            (∀j≤D,‖physical.eval (node D j:ℂ)-actual j‖ ≤ inputFee) →
            ∀x:ℝ,‖physical.eval (x:ℂ)-independent x‖≤
              (inputFee+ε*g^q/Poly.toll w s)*budget D*(1+|x|)^D := by
  classical
  obtain ⟨n,hn,dates⟩:=WilsonPositionSeparatedProfileMayerInitialLogOriginal.original R hG paid u Q cap K₀ q μ ep
  refine ⟨n,hn,?_⟩
  filter_upwards [dates] with b sale
  intro J hired A profile d hb top o ks limits hm hp ref t S P K g X W w
    F tag a inside s D actual independent physical inputFee degreeP degreeF hP x
  let filed:=WilsonFirstReceivedRadialForecast.polynomial K F tag W n s D a g
  have sourcePower (p:Hot (Stock.census V)) : W.power p=1 := rfl
  have issued : Valence.Toile W.power s (fun _=>0) := by
    intro p _
    rw [sourcePower]
    simp
  have room : (n:ℤ)+2+∑v∈s.val,(0:ℤ)≤(D:ℤ) := by simp; omega
  have value (y:ℝ) : filed.eval (y:ℂ)=independent y :=
    WilsonFirstReceivedRadialForecast.evaluated K F tag W n s D _ issued room a g y
  have ht:=Poly.worth (WilsonPositionSeparatedProfileMayerInitialLogWeights.positive
    (WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t)) s
  have nodes (j:ℕ) (hj:j≤D) : ‖actual j-independent (node D j)‖≤ε*g^q/Poly.toll w s := by
    have interval:=node_mem hj
    have admissible (e) : ‖Exterior.collect G (node D j • a) e‖≤(cap:ℝ)+1 := by
      change ‖node D j • Exterior.collect G a e‖≤_
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg interval.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) interval.2).trans (inside e)
    have observed:=sale J A profile d hb top o ks limits hm hp ref t F tag
      (node D j • a) admissible
    let U:=FundedMatchedPointOpening.colors R hG u J A d Q o μ ks profile hm hp t
    have same:Bulk.Fk K F tag U (node D j • a) n=Bulk.Fk K F tag W (node D j • a) n :=
      WilsonInitialPrescribedVacuum.original R camp hG u J A d Q o μ ks profile hm hp t F tag _ hired
    have scaled:= (Poly.member (WilsonPositionSeparatedProfileMayerInitialLogWeights.positive
      (WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t)) s _).trans
        observed.2.1
    apply (le_div_iff₀ ht).2
    rw [mul_comm]
    change Poly.toll w s * ‖(Local.cumulant P X S (Integral.sample g (node D j • a))).part s-
      (Order.value (g:ℂ) (Order.logMarked (Bulk.Fk K F tag W (node D j • a) n))).part s‖≤_
    rw [← same]
    exact scaled
  have degreeDiff: (physical-filed).natDegree≤D :=
    (Polynomial.natDegree_sub_le ..).trans (max_le degreeP
      (WilsonFirstReceivedRadialForecast.bounded K F tag W n s D a g))
  have tri (a b c:ℂ) : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  have sampled (j:ℕ) (hj:j≤D) :
      ‖(physical-filed).eval (node D j:ℂ)‖ ≤ inputFee+ε*g^q/Poly.toll w s := by
    rw [Polynomial.eval_sub,value]
    exact (tri _ (actual j) _).trans (add_le_add (hP j hj) (nodes j hj))
  simpa only [Polynomial.eval_sub,value] using priced (physical-filed) degreeDiff sampled x

end YM.Integration.WilsonFirstReceivedRadialComparison
