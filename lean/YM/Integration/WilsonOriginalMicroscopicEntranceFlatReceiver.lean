import YM.Integration.WilsonOriginalMicroscopicEntranceFlatRoster
import YM.Integration.WilsonOriginalMicroscopicEntranceGridPurchase

/-! The already purchased coordinate, store, hard and fieldwise readings
are the ones used in the older masked measurement. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatReceiver
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
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family
local notation "A" => (C₀).path.levels
local notation "J" => Stock.census (Fin 3)



def AllFields (d:Fin 3→ℕ){f n N p:ℕ}(live:f+n≤N)(Y v:∀a:Fin 3,(C₀).label (d a))
    (o:Fin 3→Site ((C₀).side f p))(Z:∀a:Fin 3,store C₀ (d a) p f):Prop:=
  let fk:f≤f+n:=Nat.le_add_right f n
  ∀(s:(J).Mode){u:ℕ}(uf:u≤f)(W:Config G ((C₀).side u p)),
    let final:=actualTransport C₀ (N:=N) (account R d live Y o v Z s) uf W
    let upper:=pin R (fk.trans live) o
    let sites:=pin R fk o
    read R d Y upper live (uf.trans fk) (guarded R d N p (f+n) sites v) s W=final ∧
      read R d Y upper live (uf.trans fk) (raw R d N p (f+n) sites v) s W=
        final-units R d (f+n) s*actualTransport C₀ (N:=N) (gap R d N p (f+n) sites v s.val) (uf.trans fk) W

def Appraised (φ:Test 3)(c q ℓ onset:ℕ)(d:Fin 3→ℕ){f n N p:ℕ}(live:f+n≤N)
    (Y seat:∀a:Fin 3,(C₀).label (d a))(V:Fin 3→ℝ)(loc:Site ((C₀).side N p)×Site ((C₀).side N p))
    (Z:∀a:Fin 3,store C₀ (d a) p f):Prop:=
  let K:=f+n
  let fk:f≤K:=Nat.le_add_right f n
  let o:=origins R (atOrigin loc) f
  ∀j≥onset,∀height:j+2≤f,(f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda A f)+2 → 0≤((A).budget f).supportExponent-2 →
  ∀t:ℝ,|t|≤(C₀).S.a (j+1)→mass (R:=R) t (N,p) φ loc≠0 →
  ∀m k (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((C₀).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ→m≤f→
  ∀(T I I':Type)[Countable I][Countable I'](L:Lamps T I G (Ψ f).p o J)(M:Lamps T I' G (Ψ f).p o J)
    (w:Fin 3→ℝ),(∀a,0<w a)→(∀a,(w a)⁻¹≤((A).clock.hatBeta f)^ℓ)→
  L.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→M.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→
  ∀u,(C₀).ref 0≤u→∀uj:u≤j,Opened C₀ 0 u p→Opened C₀ 0 j p→∀x:T,∀s:(J).Mode,
    let uf:=uj.trans (show j≤f by omega)
    let E:=fun a U=>share (fun i=>(L.log x U).part ((J).fire i)) (fun i=>(M.log x U).part ((J).fire i)) a s
    let remaining:=actualTransport C₀ (N:=N) (remainder R d live Y o seat Z s E) uf 1
    let repair:=units R d K s*actualTransport C₀ (N:=N) (gap R d N p K (pin R fk o) seat s.val) (uf.trans fk) 1
    let amount:=∑a∈s.val,4*(((A).clock.hatBeta f)^q)⁻¹*(V a*WilsonOriginalMicroscopicEntrancePeerChart.tariff G (d a))
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (guarded R d N p K (pin R fk o) seat) s 1-remaining‖≤amount ∧
    ‖read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (raw R d N p K (pin R fk o) seat) s 1-(remaining-repair)‖≤amount

def Issued (φ:Test 3)(c q ℓ onset:ℕ)(d b:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a))
    {f n N p:ℕ}(live:f+n≤N)(D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a))(V fees:Fin 3→ℝ):Prop:=
  let high:=fun a=>Y a (N,p)
  let v:=coord R d b Y D N p
  let B:=slotFare R d f (f+n) v
  ∀loc:Site ((C₀).side N p)×Site ((C₀).side N p),
    let o:=origins R (atOrigin loc) f
    ∃Z:∀a:Fin 3,store C₀ (d a) p f,WilsonOriginalMicroscopicEntranceGridStock.Filed R d (N:=N) (n:=n) high o v B Z ∧
      (∀a,Earned R (d a) N p f (o a) (Z a) (B a) (fees a)) ∧ AllFields R d live high v o Z ∧
      Appraised R φ c q ℓ onset d live high v V loc Z

theorem original (simple:G.Simple)(cater:Cater C₀ R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready A)
    (book:WilsonReportLampForecast.Ready A)(φ:Test 3)(c q r cap ℓ:ℕ)(d:Fin 3→ℕ)(grade:∀a,d a≤cap)
    {deg:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (deg a))(pt:Fin 3→Chamber):
    ∃onset:ℕ,∀(b:Fin 3→ℕ),(∀a,onset≤b a)→∀target η (Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)) f n N p
    (live:f+n≤N)(prior:∀a,b a≤f),(∀a,(C₀).ref (d a)≤f)→∀D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a),
    (∀a x,Arrived R (d a) (b a) (f+n) N p target (Nat.le_add_right_of_le (prior a)) live η (D a) x)→
    ∀V fees:Fin 3→ℝ,(∀a,0≤V a)→
    (∀a,WilsonReflectedAffordableArm.charge R (d a) f*(slotFare R d f (f+n) (coord R d b Y D N p) a)
       ≤((C₀).S.a f)^(d a)*((((A).clock.hatBeta f)^(q+2*ℓ+cap))⁻¹*V a))→
    Qualified R d b Y f n N p live D fees→Issued R φ c q ℓ onset d b Y (p:=p) live D V fees:=by
  obtain ⟨onset,sale⟩:=WilsonOriginalMicroscopicEntranceFlatRoster.original R simple cater bank book φ c q r cap ℓ d grade κ pt
  refine ⟨onset,?_⟩
  intro b starts target η Y f n N p live prior mature D arrived V fees vp salary purchased
  let high:=fun a:Fin 3=>Y a (N,p)
  let seat:=coord R d b Y D N p
  let fk:f≤f+n:=Nat.le_add_right f n
  intro loc o
  obtain ⟨Z,filed,fare,all⟩:=purchased o
  refine ⟨Z,filed,fare,all,?_⟩
  intro j late height window width t rise supported m k π Γ Ψ path enrolled
    T I I' _ _ L M w pos aperture lamp₁ lamp₂ u base uj ou oj x s
  let y:=fun a=>((C₀).factory (d a) N p).terminal.symm (high a)
  let e:=fun a=>page (C:=C₀) (d a) p (b a) (((C₀).factory (d a) N p).entries (b a) (y a))
  have agreed:(fun a:Fin 3=>(D a).symm (e a))=seat:=by
    funext a
    apply congrArg ((D a).symm)
    exact (WilsonOriginalMicroscopicGuardedPage.page_at R (d a) ((prior a).trans (fk.trans live)) (high a)).symm
  have grant:=sale j late b starts N p f n height live window width t rise loc supported m k π Γ Ψ path enrolled
    T I I' L M w pos aperture lamp₁ lamp₂ prior mature target η high D (fun a=>arrived a (e a)) V vp
  dsimp only at grant
  rw [agreed] at grant
  exact grant salary Z filed u base uj ou oj x s

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatReceiver
end
