import YM.Integration.WilsonOriginalMicroscopicEntranceFlatBalance
import YM.Integration.WilsonOriginalMicroscopicEntranceFlatPeer

/-! A single actual physical flat ear receives the three independently tuned,
fully charged upper columns. It retains the unpaid mixed shares by their original formula. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatRoster
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCompanionFace
open WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open WilsonOriginalCompanionCellRoots WilsonThermometerOwnOffsetJoint
open Extraction Cells XSpace WilsonThermometerAlignedCells
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedReporters WilsonThermometerUnitFilingFieldRange
open WilsonCoeffUV.Embroider
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicEntranceGridStock (Filed)
open WilsonOriginalMicroscopicEntranceResidualStock (remainder)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded gap)
open WilsonOriginalMicroscopicEntranceFiling (units)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family
local notation "A" => (C₀).path.levels
local notation "J" => Stock.census (Fin 3)


theorem original (simple:G.Simple)(cater:Cater C₀ R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready A)
    (book:WilsonReportLampForecast.Ready A)(φ:Test 3)(c q r cap ℓ:ℕ)(d:Fin 3→ℕ)(grade:∀a,d a≤cap)
    {deg:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (deg a))(pt:Fin 3→Chamber):
    ∃onset:ℕ,∀j≥onset,∀b:Fin 3→ℕ,(∀a,onset≤b a)→∀N p f n (height:j+2≤f)(live:f+n≤N),
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda A f)+2 → 0≤((A).budget f).supportExponent-2 →
    ∀t:ℝ,|t|≤(C₀).S.a (j+1)→∀loc:Site ((C₀).side N p)×Site ((C₀).side N p),mass (R:=R) t (N,p) φ loc≠0 →
    let o:=origins R (atOrigin loc) f
    ∀m k (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((C₀).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ→m≤f→
    ∀(T I I':Type)[Countable I][Countable I'](L:Lamps T I G (Ψ f).p o J)(M:Lamps T I' G (Ψ f).p o J)
      (w:Fin 3→ℝ),(∀a,0<w a)→(∀a,(w a)⁻¹≤((A).clock.hatBeta f)^ℓ)→
    L.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→M.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→
    ∀(prior:∀a,b a≤f), (∀a,(C₀).ref (d a)≤f)→∀target η
      (Y:∀a:Fin 3,(C₀).label (d a))(D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a)),
    let K:=f+n
    let fk:f≤K:=Nat.le_add_right f n
    let y:=fun a=>((C₀).factory (d a) N p).terminal.symm (Y a)
    let e:=fun a=>page (C:=C₀) (d a) p (b a) (((C₀).factory (d a) N p).entries (b a) (y a))
    let seat:=fun a=>(D a).symm (e a)
    let H:=WilsonOriginalMicroscopicEntranceGridBalance.slotFare R d f K seat
    (∀a,Arrived R (d a) (b a) K N p target ((prior a).trans fk) live η (D a) (e a))→
    ∀V:Fin 3→ℝ,(∀a,0≤V a)→
    (∀a,WilsonReflectedAffordableArm.charge R (d a) f*H a≤((C₀).S.a f)^(d a)*((((A).clock.hatBeta f)^(q+2*ℓ+cap))⁻¹*V a))→
    ∀Z:∀a:Fin 3,store C₀ (d a) p f,WilsonOriginalMicroscopicEntranceGridStock.Filed R d (N:=N) (n:=n) Y o seat H Z→
    ∀u,(C₀).ref 0≤u→∀uj:u≤j,Opened C₀ 0 u p→Opened C₀ 0 j p→∀x:T,∀s:(J).Mode,
    let uf:=uj.trans (show j≤f by omega)
    let E:=fun a U=>share (fun i=>(L.log x U).part ((J).fire i)) (fun i=>(M.log x U).part ((J).fire i)) a s
    let remaining:=actualTransport C₀ (N:=N) (remainder R d live Y o seat Z s E) uf 1
    let repair:=units R d K s*actualTransport C₀ (N:=N) (gap R d N p K (pin R fk o) seat s.val) (uf.trans fk) 1
    let amount:=∑a∈s.val,4*(((A).clock.hatBeta f)^q)⁻¹*(V a*WilsonOriginalMicroscopicEntrancePeerChart.tariff G (d a))
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (guarded R d N p K (pin R fk o) seat) s 1-remaining‖≤amount ∧
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (raw R d N p K (pin R fk o) seat) s 1-(remaining-repair)‖≤amount:=by
  choose floor applyPaid using fun a=>WilsonOriginalMicroscopicEntranceFlatPeer.original R simple cater bank book φ c q r cap (d a) ℓ (grade a)
  let start:=Finset.univ.sup floor
  have each (a:Fin 3):floor a ≤ start:=Finset.le_sup (Finset.mem_univ a)
  refine ⟨start,?_⟩
  intro j early b banks N p f n height live window width t rise loc supported o m k π Γ Ψ path enrolled
    T I I' _ _ L M w pos aperture lamp₁ lamp₂ prior mature target η Y D K fk y e seat H arrived V vp salary Z filed
    u base uj opened heads x s uf E remaining repair amount
  apply WilsonOriginalMicroscopicEntranceFlatBalance.original R d live Y o seat H Z κ pt mature filed s
    (fun U i=>(L.log x U).part ((J).fire i)) (fun U i=>(M.log x U).part ((J).fire i))
    (fun a=>4*(((A).clock.hatBeta f)^q)⁻¹*(V a*WilsonOriginalMicroscopicEntrancePeerChart.tariff G (d a))) uf 1
  intro a used
  exact applyPaid a j ((each a).trans early) (b a) ((each a).trans (banks a)) N p f height (fk.trans live)
    window width t rise loc supported m k π Γ Ψ path enrolled T I I' L M w pos aperture lamp₁ lamp₂ a K
    ((prior a).trans fk) live (prior a) fk target η (D a) (y a) (arrived a) u base uj opened heads x s used
    (Z a) (filed a) (V a) (vp a) (salary a)

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatRoster
end
