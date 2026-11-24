import YM.Integration.WilsonOriginalMicroscopicEntranceMaskDebt
import YM.Integration.WilsonOriginalMicroscopicEntranceHaloIncome
import YM.Integration.WilsonOriginalMicroscopicEntranceFlatPublic

/-! Purchase of the uncut original three-stencil reading under the true stopped Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatWithdrawal
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
open AllOrder.Transit WheelP Org AnalyticBridge VerifiedReset QuadraticLocal.Affinity
open WilsonOriginalMicroscopicEntranceMaskDebt (debit)
open WilsonOriginalMicroscopicEntranceGridRow (old entered)
open WilsonOriginalMicroscopicEntranceMarginals (Spent Cleared)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family
local notation "A" => (C₀).path.levels
local notation "J" => Stock.census (Fin 3)




def halo (d:Fin 3→ℕ)(K:ℕ)(V:Fin 3→ℝ)(tol:ℝ)(q:ℕ)(s:(J).Mode):ℝ:=
  WilsonOriginalMicroscopicEntranceOpticalUnits.fare R d V s*((WilsonOriginalMicroscopicGuardedFlat.count R d s.val:ℝ)*
    (4*Real.exp (((A).budget K).supportExponent+2)*(tol/((A).clock.hatBeta K)^q)))

theorem fee (f e:ℕ)(d:Fin 3→ℕ)(cash V:Fin 3→ℝ)(paid:∀a,0 ≤ cash a)(vp:∀a,0 ≤ V a)(a:Fin 3):
    cash a*(((A).clock.hatBeta f)^e)⁻¹*((C₀).S.a f)^(d a)*V a ≤ ((C₀).S.a f)^(d a)*(cash a*V a):=by
  have one:1 ≤ ((A).clock.hatBeta f)^e:=one_le_pow₀ ((A).fits.delayed f).le
  calc _ = (((C₀).S.a f)^(d a)*(cash a*V a))*(((A).clock.hatBeta f)^e)⁻¹ :=by ring
       _  ≤  _:=mul_le_of_le_one_right (mul_nonneg (pow_nonneg ((C₀).S.a_pos f).le _) (mul_nonneg (paid a) (vp a))) (inv_le_one_of_one_le₀ one)

def Heard (φ:Test 3)(simple:G.Simple)(tol:ℝ)(c q ℓ onset:ℕ)(d:Fin 3→ℕ){f n N p:ℕ}(live:f+n ≤ N)
    (Y seat:∀a:Fin 3,(C₀).label (d a))(V:Fin 3→ℝ)(loc:Site ((C₀).side N p)×Site ((C₀).side N p))
    :Prop:=
  let K:=f+n
  let fk:f ≤ K:=Nat.le_add_right f n
  let o:=origins R (atOrigin loc) f
  ∀j≥onset,∀height:j+2 ≤ f,(f-(j+2):ℕ) ≤ (c:ℝ)*Real.log (RG16.Lambda A f)+2 → 0 ≤ ((A).budget f).supportExponent-2 →
  ∀t:ℝ,|t| ≤ (C₀).S.a (j+1)→mass (R:=R) t (N,p) φ loc≠0 →
  ∀m k (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((C₀).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ→m ≤ f→Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N)→
  ∀(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls),TicketP R.alloy R.kit D Q→
  ∀(T I I':Type)[Countable I][Countable I'](L:Lamps T I G (Ψ f).p o J)(M:Lamps T I' G (Ψ f).p o J)
    (w:Fin 3→ℝ),(∀a,0<w a)→(∀a,(w a)⁻¹ ≤ ((A).clock.hatBeta f)^ℓ)→
  L.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→M.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1→
  ∀u,(C₀).ref 0 ≤ u→∀uj:u ≤ j,Opened C₀ 0 u p→Opened C₀ 0 j p→m ≤ u→WilsonSingleHardRadius.first R simple ≤ u→
    WilsonCenteredCaptureClock.first R simple ≤ K→∀x:T,∀s:(J).Mode,
    let uf:=uj.trans (show j ≤ f by omega)
    let FN:=old R d (fk.trans live) Y o
    let FK:=entered R d (N:=N) (n:=n) o seat
    let first:=fun U i=>(L.log x U).part ((J).fire i)
    let second:=fun U i=>(M.log x U).part ((J).fire i)
    let E:=fun a U=>share (first U) (second U) a s
    let remaining:=actualTransport C₀ (N:=N) (fun U=>debit R (N:=N) FN (fk.trans live) first E s U-
        debit R (N:=N) FK fk second E s U) uf 1
    let amount:=∑a∈s.val,4*(((A).clock.hatBeta f)^q)⁻¹*(V a*WilsonOriginalMicroscopicEntrancePeerChart.tariff G (d a))
    let extra:=halo R d K V tol q s
    let value:=read R d Y (pin R (fk.trans live) o) live (uf.trans fk) (raw R d N p K (pin R fk o) seat) s 1
    ‖value-remaining‖ ≤ amount+extra ∧ (Basic s→‖value‖ ≤ amount+extra)

def Returned (φ:Test 3)(simple:G.Simple)(tol:ℝ)(c q ℓ onset:ℕ)(d b:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a))
    {f n N p:ℕ}(live:f+n ≤ N)(D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a))(V fees:Fin 3→ℝ):Prop:=
  let high:=fun a=>Y a (N,p)
  let v:=coord R d b Y D N p
  let B:=slotFare R d f (f+n) v
  ∀loc:Site ((C₀).side N p)×Site ((C₀).side N p),
    let o:=origins R (atOrigin loc) f
    ∃Z:∀a:Fin 3,store C₀ (d a) p f,WilsonOriginalMicroscopicEntranceGridStock.Filed R d (N:=N) (n:=n) high o v B Z ∧
      (∀a,Earned R (d a) N p f (o a) (Z a) (B a) (fees a)) ∧ AllFields R d live high v o Z ∧
      Appraised R φ c q ℓ onset d live high v V loc Z ∧ Cleared R φ c q ℓ onset d live high v V loc ∧
      Heard R φ simple tol c q ℓ onset d live high v V loc



private theorem reunited (a b c:ℂ):‖a-b‖ ≤ ‖a-(b-c)‖+‖c‖:=by
  simpa only [show a-(b-c)-c=a-b by ring] using norm_sub_le (a-(b-c)) c

theorem original {φ:Test 3}{c q ℓ onset:ℕ}{d b:Fin 3→ℕ}{Y:∀a:Fin 3,ℕ×ℕ→(C₀).label (d a)}
    {f n N p t:ℕ}{live:f+n ≤ N}{D:∀a:Fin 3,(C₀).label (d a)≃ₗ[ℂ](C₀).label (d a)}{V fees:Fin 3→ℝ}
    (simple:G.Simple){tol:ℝ}(positive:0<tol)(vp:∀a,0 ≤ V a)(budget:∀a,fees a ≤ ((C₀).S.a f)^(d a)*V a)
    (mature:∀a,(C₀).ref (d a) ≤ f)(housing:(C₀).S.a f/(C₀).S.a (f+n) ≤ ((A).clock.hatBeta (f+n))^t)
    (late:(Filter.eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (q+WilsonOriginalMicroscopicEntranceHaloIncome.all R d t) positive)).choose ≤ f+n)
    (bought:Spent R φ c q ℓ onset d b Y (p:=p) live D V fees):
    Returned R φ simple tol c q ℓ onset d b Y (p:=p) live D V fees:=by
  intro loc o
  obtain ⟨Z,filed,earned,every,assay,cleared⟩:=bought loc
  refine ⟨Z,filed,earned,every,assay,cleared,?_⟩
  intro j je height window width t' rise support m k π Γ Ψ course enrolled top way roots Q ticket
    T I I' _ _ L M w wp wbound left right u ur uj uok jok prior fixed capture x s
  letI : Nonempty T:=⟨x⟩
  let fk:=Nat.le_add_right f n
  have uf:u ≤ f:=by omega
  let v:=coord R d b Y D N p
  let upper:=fun a=>Y a (N,p)
  let leftArm:=fun U i=>(L.log x U).part ((J).fire i)
  let rightArm:=fun U i=>(M.log x U).part ((J).fire i)
  let E:=fun a U=>share (leftArm U) (rightArm U) a s
  let hot:=units R d (f+n) s*actualTransport C₀ (N:=N) (gap R d N p (f+n) (pin R fk o) v s.val) (uf.trans fk) 1
  have pay:‖hot‖ ≤ halo R d (f+n) V tol q s:=
    WilsonOriginalMicroscopicEntranceHaloIncome.original R d π Γ Ψ course live top simple way roots Q ticket
      prior (uf.trans fk) fixed capture fk housing (pin R fk o) v V vp (fun a=>(earned a).1.trans (budget a))
      q positive late s le_rfl (by omega)
  let value:=read R d upper (pin R (fk.trans live) o) live (uf.trans fk) (raw R d N p (f+n) (pin R fk o) v) s 1
  let remaining:=actualTransport C₀ (N:=N) (remainder R d live upper o v Z s E) uf 1
  have parts:=assay j je height window width t' rise support m k π Γ Ψ course enrolled
    T I I' L M w wp wbound left right u ur uj uok jok x s
  have bill:= (reunited value remaining hot).trans (add_le_add parts.2 pay)
  have eq:remainder R d live upper o v Z s E=
      fun U=>debit R (N:=N) (old R d (fk.trans live) upper o) (fk.trans live) leftArm E s U-
        debit R (N:=N) (entered R d (N:=N) (n:=n) o v) fk rightArm E s U:=by
    funext U
    exact WilsonOriginalMicroscopicEntranceMaskDebt.original R d live upper o v _ Z mature filed leftArm rightArm s U
  change ‖_-actualTransport C₀ (N:=N) (remainder R d live upper o v Z s E) uf 1‖ ≤ _ at bill
  rw [eq] at bill
  refine ⟨bill,?_⟩
  intro elementary
  have base:=cleared j je height window width t' rise support m k π Γ Ψ course enrolled T I I' L M
    w wp wbound left right u ur uj uok jok s elementary
  have last:=norm_sub_le (value+hot) hot
  have cost:=last.trans (add_le_add base.2 pay)
  simpa only [add_sub_cancel_right] using cost
end YM.Integration.WilsonOriginalMicroscopicEntranceFlatWithdrawal
end
