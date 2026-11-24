import YM.Integration.WilsonOriginalCompoundPositionElection
import YM.Integration.WilsonThermometerUnitFilingWeakStrip
import YM.Integration.WilsonPhysicalHistoryPriorAperture

/-! Price the actual public student's dated spatial width in the same before-length election as the smaller older comparison school. Increasing the sheet's length floor retains the canonical roots of the public school. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCampus
open Function Filter Finset Lattice RG RG16 RG.Shoot RG.Supply Wilson Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore QuadraticLocal.Syl
open WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalCompoundStrip WilsonWindowRootPurchase
open scoped Classical BigOperators
universe u
variable {G:Gauge}
abbrev Seats (j:ℕ):=Fin (j+2)×Fin (j+2)×Fin 2

def raw (simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)(j:ℕ)(c:Seats j):ℝ:=
  Poetry.Agenda.seed (roots simple s pr) (φ c.1) (Burn.horizon c.2.1) (j+c.2.2)

theorem positive (simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)(j:ℕ)(c:Seats j):
    0<raw simple φ s pr j c:=Poetry.Agenda.stem _ _ _ _

def reserve (simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)(j:ℕ):ℝ:=
  (1+∑c:Seats j,(raw simple φ s pr j c)⁻¹)⁻¹

theorem room (simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)(j:ℕ):
    0<reserve simple φ s pr j ∧ ∀c,reserve simple φ s pr j≤raw simple φ s pr j c:=by
  have all(c:Seats j):0 < (raw simple φ s pr j c)⁻¹:=inv_pos.mpr (positive ..)
  have non:0≤∑c:Seats j,(raw simple φ s pr j c)⁻¹:=sum_nonneg (fun c _=>(all c).le)
  refine ⟨inv_pos.mpr (by linarith),?_⟩
  intro c
  have member: (raw simple φ s pr j c)⁻¹≤∑x:Seats j,(raw simple φ s pr j x)⁻¹:=
    single_le_sum (fun x _=>(all x).le) (mem_univ c)
  exact (inv_anti₀ (all c) (show (raw simple φ s pr j c)⁻¹≤1+∑x:Seats j,(raw simple φ s pr j x)⁻¹ by linarith)).trans (inv_inv _).le

def seated (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices):Request G where
  radius K j H:=min (Q.radius K j H) (reserve simple φ s pr j)
  positive K j H:=lt_min (Q.positive K j H) (room simple φ s pr j).1
  multiplier:=Q.multiplier
  grows:=Q.grows
  entrance:=Q.entrance

def syllabus (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices):Request G:=
  WilsonThermometerUnitFilingWeakStrip.enrolled (WilsonOriginalCompoundVertexStrip.narrowed (seated Q simple φ s pr))

def Invoice (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ):Prediction G:=fun {M} {_} {_} w=>
  WilsonOriginalCompoundPositionElection.Invoice (syllabus Q simple φ M.p M.K) w

private theorem raised (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)
    (l:ℕ→ℕ):syllabus Q simple φ (ThroughLaunch.raise s l) pr=syllabus Q simple φ s pr:=rfl

theorem prepaid (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ):
    WilsonFundedWindowMenu.AllPrices (@Invoice G Q simple φ):=by
  intro s pr targets expenses chartEq programs z bt
  let price:=raging s pr
  obtain ⟨floor,hi⟩:=WilsonOriginalCompoundPositionElection.prepaid (syllabus Q simple φ s price) simple s pr
    targets expenses chartEq programs z bt
  refine ⟨floor,?_⟩
  intro l hl D w U Z φ' S pocket θ p P menu V quarter
  obtain ⟨W,later,issue⟩:=hi l hl D w U Z φ' S pocket θ p P menu V quarter
  refine ⟨W,later,?_⟩
  intro W' step K I hp B0 archive origins port A η q E' J K' b hZ hY hm
  change WilsonOriginalCompoundPositionElection.Invoice (syllabus Q simple φ (ThroughLaunch.raise s l) price) _
  rw [raised]
  exact issue W' step K I hp B0 archive origins port η q E' J K' b hZ hY hm

noncomputable abbrev funded (Q:Request G)(φ:ℕ→ℕ→ℕ)(cap U:ℕ→ℕ)(mono:Monotone cap)
    (simple:G.Simple){ε:ℝ}(pos:0<ε):=
  WilsonOriginalCompoundPositionElection.withSupplement.{u} Q (@Invoice G Q simple φ)
    (prepaid Q simple φ) cap U mono simple pos

theorem date (Q:Request G)(R:Run G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)
    (paid:Invoice Q simple φ R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i):
    let X:=syllabus Q simple φ R.metals.p R.metals.K
    let j:=R.alloy.B.a.clock.J i
    let K:=R.metals.p.kernel
    let μ:=width X K j H
    0<μ ∧ μ≤1 ∧ Real.exp (μ⁻¹^2)≤R.alloy.B.a.clock.hatBeta i ∧
    (∀c:Seats j,μ≤raw simple φ R.metals.p R.metals.K j c/(16*Q.multiplier H)) ∧
    ∀s:ℕ,s≤j+1→WilsonOlderFreshGraphCappedPrice.factor
      (WilsonOlderFreshGraphCappedPrice.degree s (R.alloy.B.a.budget i).power (R.alloy.B.a.budget i).order)
      (μ/4)≤budgetR R i:=by
  intro X j K μ
  obtain ⟨_,good,one,top,beta,cash⟩:=WilsonOriginalCompoundStrip.date X R paid.1.1 i H fit
  refine ⟨good,one,beta,?_,cash⟩;intro c
  have stripped:X.radius K j H≤raw simple φ R.metals.p R.metals.K j c:=by
    exact (min_le_left ..).trans ((min_le_left ..).trans ((min_le_right ..).trans ((room simple φ _ _ j).2 c)))
  have mult:Q.multiplier H≤X.multiplier H:=le_max_right .. 
  exact top.trans ((div_le_div_of_nonneg_right stripped (mul_nonneg (by norm_num) (X.grows H).le)).trans
    (div_le_div_of_nonneg_left (positive ..).le (mul_pos (by norm_num) (Q.grows H))
      (mul_le_mul_of_nonneg_left mult (by norm_num))))

end YM.Integration.WilsonThermometerUnitFilingCampus
