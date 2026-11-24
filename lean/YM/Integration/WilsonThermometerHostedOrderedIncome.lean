import YM.Integration.WilsonThermometerHostedPeerSoft
import YM.Integration.WilsonOriginalCompanionLowerMaterial

/-! The full canonical signed coefficient heard on the ordinary peer pair with its own hard catalogue. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerHostedOrderedIncome
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCompanionFace
open WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open WilsonOriginalCompanionCellRoots WilsonThermometerOwnOffsetJoint
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "J"=>Stock.census (Fin 3)
open Extraction Cells XSpace WilsonThermometerAlignedCells



theorem restore {N p f u:ℕ}(uf:u≤f)(Z D S:Config G ((CF).side f p)→ℂ)
    (linked:∀U,Z U=D U+S U)(w:ℝ)(wp:0≤w)(B C:ℝ)
    (debt:Integrable D (prior G _) ∧ w*‖reading R (N:=N) (p:=p) D u uf‖≤B)
    (soft:Integrable S (prior G _) ∧ w*‖reading R (N:=N) (p:=p) S u uf‖≤C):
    Integrable Z (prior G _) ∧ w*‖reading R (N:=N) (p:=p) Z u uf‖≤B+C:=by
  have eq:Z=D+S:=funext linked
  have good:Integrable Z (prior G _):=eq ▸ debt.1.add soft.1
  have delta:(fun U=>Z U-S U)=D:=by funext U;rw [linked];ring
  have read:=WilsonMeasuredCompanionTransport.subtract R (N:=N) Z S good soft.1 uf
  rw [delta] at read
  have together:=sub_eq_iff_eq_add.mp read.symm
  refine ⟨good,?_⟩
  rw [together]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) wp).trans
    ((mul_add _ _ _).le.trans (add_le_add debt.2 soft.2))
theorem original (simple:G.Simple)(cater:Cater (CF) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(book:WilsonReportLampForecast.Ready (A))
    (φ:Test 3)(c q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p f (height:j+2≤f) (_:f≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 → 0≤((A).budget f).supportExponent-2 →
    ∀r:ℝ,|r|≤(CF).S.a (j+1) →
    ∀y:Site ((CF).side N p)×Site ((CF).side N p),mass (R:=R) r (N,p) φ y≠0 →
    let o:=origins R (atOrigin y) f
    let P:=(CF).path.rep N p f
    ∀(m k:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((CF).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ → m≤f →
    ∀(T I I':Type)[Countable I][Countable I'](a:Lamps T I G (Ψ f).p o (J))
      (b:Lamps T I' G (Ψ f).p o (J))(w:Fin 3→ℝ),(∀v,0<w v) →
    a.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 → b.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 →

    ∀(v:Fin 3){d:ℕ}(h:Coefficient ((CF).labels.level d) ((CF).side f p))(B:ℝ),0≤B →
      h.Format (o v) (CF).params P → h.remBound (o v) P (LocalComparison.forcedDivisor (CF) f) B →
    ∀u:ℕ,(CF).ref 0≤u → ∀uj:u≤j,Opened (CF) 0 u p → Opened (CF) 0 j p →
    ∀(x:T)(s:(J).Mode),v∈s.val →
    let Y:=fun U=>h.density (o v) ((CF).localSection d) P U*
      share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s
    Integrable Y (prior G _) ∧ companions v (Stoop.radius w 2) s*‖reading R (N:=N) (p:=p) Y u (uj.trans (by omega))‖≤
      WilsonOriginalCompanionLowerPeer.tariff*B*(regulatorRun (CF) N p f)^q+
      (WilsonThermometerUnitFilingFieldRange.cost G d P.p.threshold*((CF).labels.level d).coeffSize h.x+B)*WilsonMeasuredCompanionSoft.expense 1:=by
  filter_upwards [WilsonOriginalCompanionLowerMaterial.original R simple cater bank book φ c q] with j spent
  intro N p f height fn days expo r span y active o P m k π Γ Ψ course mf T I I' ca cb a b w pos pa pb v d h B bp fmt bill
    u ref uj ou oj x s inside Y
  let uf:u≤f:=uj.trans (by omega)
  let peer (U:Config G ((CF).side f p)):= share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(b.log x U).part ((J).fire i)) v s
  let softPart (U:Config G ((CF).side f p)):=(soft h).density (o v) ((CF).localSection d) P U*peer U
  let hardPart (U:Config G ((CF).side f p)):=(h.density (o v) ((CF).localSection d) P U-
       (soft h).density (o v) ((CF).localSection d) P U)*peer U
  have hrd:=spent N p f height fn days expo r span y active m k π Γ Ψ course mf T I I' a b w pos pa pb v h (CF).params
    ((CF).localSection d) B bp fmt bill (fun _:T=>(1:ℂ)) (by simp) u ref uj ou oj x s inside
  simp only [one_mul] at hrd
  have same:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course mf fn).1
  have law:=((R.T.sticks N p).prices f (Nat.zero_le _) fn).1.valid
  have sft:=WilsonThermometerHostedPeerSoft.original R P (Ψ f) same rfl ⟨_,_,_,_,_,law⟩ fn uf a b w pos expo pa pb v h fmt bill x s inside
  have identity (U):Y U=hardPart U+softPart U:=by
    change _*peer U=(_-_)*peer U+_*peer U
    ring
  exact restore R uf Y hardPart softPart identity _ (Finset.prod_nonneg fun i _=>div_nonneg (pos i).le (by norm_num)) _ _ hrd sft

end YM.Integration.WilsonThermometerHostedOrderedIncome
