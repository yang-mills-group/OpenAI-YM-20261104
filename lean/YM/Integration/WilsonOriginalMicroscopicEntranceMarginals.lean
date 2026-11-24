import YM.Integration.WilsonOriginalMicroscopicEntranceFlatReceiver
import YM.Integration.WilsonOriginalMicroscopicEntrancePureModes

/-! The four lower modes have no mixed remainder at any original field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceMarginals
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
open WilsonOriginalMicroscopicEntranceGridCensus (Earned Qualified)
open WilsonOriginalMicroscopicEntranceGridBalance (coord slotFare)
open WilsonOriginalMicroscopicEntranceGridStock (account)
open WilsonOriginalMicroscopicEntranceFlatReceiver (Appraised AllFields Issued)
open WilsonOriginalMicroscopicEntrancePureModes (Basic)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family
local notation "A" => (C₀).path.levels
local notation "J" => Stock.census (Fin 3)



def Cleared (φ:Test 3)(c q ℓ onset:ℕ)(d:Fin 3→ℕ){f n N p:ℕ}(live:f+n≤N)
    (Y seat:∀a:Fin 3,(C₀).label (d a))(V:Fin 3→ℝ)(loc:Site ((C₀).side N p)×Site ((C₀).side N p)):Prop:=
  let K:=f+n
  let fk:f≤K:=Nat.le_add_right f n
  let o:=origins R (atOrigin loc) f
  ∀j≥onset,∀height:j+2≤f,(f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda A f)+2 → 0≤((A).budget f).supportExponent-2 →
  ∀t:ℝ,|t|≤(C₀).S.a (j+1)→mass (R:=R) t (N,p) φ loc≠0 →
  ∀m k (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((C₀).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ→m≤f→
  ∀(T I I':Type)[Nonempty T][Countable I][Countable I'](L:Lamps T I G (Ψ f).p o J)(M:Lamps T I' G (Ψ f).p o J)
    (w:Fin 3→ℝ),(∀a,0<w a)→(∀a,(w a)⁻¹≤((A).clock.hatBeta f)^ℓ)→
  L.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→M.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→
  ∀u,(C₀).ref 0≤u→∀uj:u≤j,Opened C₀ 0 u p→Opened C₀ 0 j p→∀s:(J).Mode,Basic s→
    let uf:=uj.trans (show j≤f by omega)
    let repair:=units R d K s*actualTransport C₀ (N:=N) (gap R d N p K (pin R fk o) seat s.val) (uf.trans fk) 1
    let amount:=∑a∈s.val,4*(((A).clock.hatBeta f)^q)⁻¹*(V a*WilsonOriginalMicroscopicEntrancePeerChart.tariff G (d a))
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (guarded R d N p K (pin R fk o) seat) s 1‖≤amount ∧
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (raw R d N p K (pin R fk o) seat) s 1+repair‖≤amount

def Spent (φ:Test 3)(c q ℓ onset:ℕ)(d b:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a))
    {f n N p:ℕ}(live:f+n≤N)(D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a))(V fees:Fin 3→ℝ):Prop:=
  let high:=fun a=>Y a (N,p)
  let v:=coord R d b Y D N p
  let B:=slotFare R d f (f+n) v
  ∀loc:Site ((C₀).side N p)×Site ((C₀).side N p),
    let o:=origins R (atOrigin loc) f
    ∃Z:∀a:Fin 3,store C₀ (d a) p f,WilsonOriginalMicroscopicEntranceGridStock.Filed R d (N:=N) (n:=n) high o v B Z ∧
      (∀a,Earned R (d a) N p f (o a) (Z a) (B a) (fees a)) ∧ AllFields R d live high v o Z ∧
      Appraised R φ c q ℓ onset d live high v V loc Z ∧ Cleared R φ c q ℓ onset d live high v V loc


theorem original {φ:Test 3}{c q ℓ onset:ℕ}{d b:Fin 3→ℕ}{Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)}
    {f n N p:ℕ}{live:f+n≤N}{D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a)}{V fees:Fin 3→ℝ}
    (purchased:Issued R φ c q ℓ onset d b Y (p:=p) live D V fees):
    Spent R φ c q ℓ onset d b Y (p:=p) live D V fees:=by
  intro loc o
  obtain ⟨Z,filed,fare,all,assay⟩:=purchased loc
  refine ⟨Z,filed,fare,all,assay,?_⟩
  intro j late height window width t rise support m k π Γ Ψ path enrolled T I I' _ _ _ L M
    w pos aperture lamp₁ lamp₂ u base uj ou oj s low
  let x:T:=Classical.choice inferInstance
  have owned:=assay j late height window width t rise support m k π Γ Ψ path enrolled T I I' L M
    w pos aperture lamp₁ lamp₂ u base uj ou oj x s
  let high:=fun a:Fin 3=>Y a (N,p)
  let seat:=coord R d b Y D N p
  let first:=fun U i=>(L.log x U).part ((J).fire i)
  let second:=fun U i=>(M.log x U).part ((J).fire i)
  let E:=fun a U=>share (first U) (second U) a s
  let uf:=uj.trans (show j≤f by omega)
  have cleared:actualTransport C₀ (N:=N) (remainder R d live high o seat Z s E) uf 1=0:=by
    rw [show remainder R d live high o seat Z s E=0 from
      WilsonOriginalMicroscopicEntrancePureModes.original R d live high o seat Z s low first second]
    exact actualTransport_const C₀ R.makes ((Nat.le_add_right f n).trans live) (0:ℂ) uf 1
  dsimp only at owned ⊢
  rw [cleared] at owned
  simpa only [sub_zero,zero_sub,sub_neg_eq_add] using owned

end YM.Integration.WilsonOriginalMicroscopicEntranceMarginals
end
