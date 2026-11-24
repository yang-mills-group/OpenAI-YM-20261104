import YM.Integration.WilsonOriginalFlatFiledMask
import YM.Integration.WilsonOriginalFlatGalleryHearing

/-! Price the actual filed ordinary numerator at its earlier flat receiver. The
fresh mask discrepancy is already filed on the compulsory quiet owners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatFiledHearing
open WilsonOriginalFlatFiledMask WilsonOriginalFlatOccupiedRate WilsonRootedKioskOccupiedSlip
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open Extra.Histories Multi WilsonOriginalOrdinaryFlatHulls WilsonCenteredCompleteGallery
open WilsonThermometerUnitFilingCoarse (reading)
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors
open AnalyticBridge.SectorAffine.Offset
open scoped BigOperators Classical
open private YM.Integration.WilsonOriginalOrdinaryFlatHulls.gross from YM.Integration.WilsonOriginalOrdinaryFlatHulls

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m   ≤   u)(ub:u   ≤   b)
   (fixed:WilsonSingleHardRadius.first R simple   ≤   u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance b
local notation "Space" => Config G (R.family.side b per)


private theorem toll (p:BudgetPoint){n:Side}{V:Type}[DecidableEq V][Fintype V]{J:Census V}
    (Z:Support n)(w:V→ℝ)(hw:∀a,0<w a)(s:J.Mode){E D rent v κ₀:ℝ}
    (ep:0 ≤ E)(dp:0 ≤ D)(rp:0 ≤ rent)(hv:0 ≤ v)(div:0<κ₀)(small:κ₀ ≤ 1)(room:hitWidth p*v ≤ κ₀):
    let cash:=bill p Z (E+rent) s.val.card+roof p Z E s.val.card+roof p Z D s.val.card
    WilsonFullFaceSignedHard.fee p Z w s (E+rent) κ₀ v κ₀+maskBill p Z w s E D v κ₀ ≤ 
      (Poly.toll w s)⁻¹*cash:=by
  intro cash
  have a:=WilsonOriginalFlatOccupiedRate.earned p Z w hw s (le_refl _) (add_nonneg ep rp) div small (room.trans small)
  have b:=WilsonOriginalFlatFiledMask.earned p Z w hw s ep dp hv div room (le_refl _)
  rw [←mul_le_mul_iff_right₀ (Poly.worth hw s)]
  rw [←mul_assoc,mul_inv_cancel₀ (Poly.worth hw s).ne',one_mul,mul_add]
  simpa only [cash,add_assoc] using add_le_add a b

include course cut way ticket floor ub fixed S A in
set_option maxHeartbeats 700000 in
theorem original (capture:WilsonCenteredCaptureClock.first R simple  ≤  b)(p d₀:ℕ)
    {tol:ℝ}(pos:0<tol)(hardLate:WilsonSingleHardRadius.start R simple p pos  ≤  b)
    (divLate:(eventually_atTop.mp (WilsonCenteredDividedRoom.original R simple)).choose ≤ b)
    {V X ι μ:Type}[DecidableEq V][Fintype V][Countable ι][Countable μ]{J:Census V}
    (o:V→Site (R.family.side b per))(L:Lamps X ι G (Ψ b).p o J)(Y₀:Lamps X μ G (Ψ b).p o J)
    (H:Hard X (Ψ b).p (Ψ b).activities.forced (Ψ b).activities.K o J)(x:X)(s:J.Mode)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (p+d₀*s.val.card) pos)).choose ≤ b)
    (Z:Support (R.family.side b per))(y:Site (R.family.side b per))(center:y∈Z)
    (resident:∀a∈s.val,o a∈Z)(rad:ℕ)(near:∀a∈s.val,separation (o a) y ≤ rad)
    (w:V→ℝ)(hw:∀a,0<w a){E D' rent W:ℝ}(ep:0 ≤ E)(dp:0 ≤ D')(rp:0 ≤ rent)(wp:0 ≤ W)
    (source:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹ ≤ W)
    (paid:L.Paid w (Ψ b).p.B ((Ψ b).p.supportExponent+2) E)
    (gross:Gross L w (Ψ b).p.B ((Ψ b).p.supportExponent+2) D')
    (old:Y₀.Paid w (Ψ b).p.B ((Ψ b).p.supportExponent+2) rent)
    (forced:H.Paid w (Ψ b).p.B (Ψ b).p.supportExponent κ)
    {α:ℝ}(strength:(Ψ b).p.supportExponent ≤ α)(tube:LinkTube G)(front:Hot J→V)(member:∀t,front t∈t.val.val)
    (I:Space→Poly J)(neutral:∀U,(I U).part J.quiet=0)
    (borel:Measurable (fun U=>(Poly.pass (bare L x U)).part s+
      (soft (posted L Y₀ H) x s U-(Poly.pass (L.log x U)).part s)-(Poly.pass (I U)).part s))
    {M δ:ℝ}(mp:0 ≤ M)(small:0 ≤ δ)
    (salary:∀U (t:Hot J),t.val.val⊆s.val →
      ‖(bare L x U).part t.val‖ ≤ M*β^d₀ ∧ ‖(I U).part t.val‖ ≤ M*β^d₀)
    (rows:∀(t:Hot J),t.val.val⊆s.val → WilsonOriginalOrdinaryFlatHulls.Row (Ψ b).p tube (o (front t))
      (fun U=>(bare L x U).part t.val) (fun U=>(I U).part t.val))
    (due:∀t ht,(rows t ht).price ≤ δ)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    let oldFee:=change s (W*E) (W*rent)
    let cash:=bill (Ψ b).p Z (E+rent) s.val.card+roof (Ψ b).p Z E s.val.card+roof (Ψ b).p Z D' s.val.card
    ‖reading R (N:=N) (fun U=>((posted L Y₀ H).density x U).part s-((Ψ b).eval U:ℂ)*(Poly.pass (I U)).part s)
        i ((Nat.le_succ i).trans ib)‖ ≤ 
      oldFee+change s (M*β^d₀) δ+(oldFee+2*cost s M)*s.val.card*(4*Real.exp (α+2))*tol/β^p+
        4*(1+(Poly.toll w s)⁻¹*cash)*tol/β^p:=by
  intro oldFee cash
  let A₀:=posted L Y₀ H
  let rest:=fun U:Space=>soft A₀ x s U-(Poly.pass (L.log x U)).part s
  let pure:=fun U:Space=>(Poly.pass (bare L x U)).part s-(Poly.pass (I U)).part s
  let X₀:=fun U:Space=>(Poly.pass (bare L x U)).part s+rest U-(Poly.pass (I U)).part s
  let H₀:=fun U:Space=>(A₀.density x U).part s-((Ψ b).eval U:ℂ)*((Poly.pass (bare L x U)).part s+rest U)
  let R₀:=fun U:Space=>((Ψ b).eval U:ℂ)*X₀ U
  have walk:=course.1.walk b (floor.trans ub) cut.le
  have same:(Ψ b).eval=(R.family.path.rep N per b).eval:=walk.view
  have width:0 ≤ (Ψ b).p.supportExponent+2:=by linarith only [(Ψ b).p.exponent_pos]
  have quiet (U:Space):(bare L x U).part J.quiet=0 ∧ (I U).part J.quiet=0:=
    ⟨WilsonRootedKioskCompleteFiling.quiet L hw width gross x U,neutral U⟩
  obtain ⟨keeper⟩:=WilsonCenteredCourseKeeper.original R course b (floor.trans ub) cut
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec b capture
  rw [←walk.truep.point] at room
  obtain ⟨oldPrice,q,valid,payment,field⟩:=WilsonOriginalFlatFiledMask.components (F:=F) L Y₀ H x s A Z y center
    resident rad near keeper w hw walk.truep.valid hv room div paid gross old forced source ep rp wp
  have op:0 ≤ oldFee:=(norm_nonneg (rest 1)).trans (oldPrice 1)
  have inc:1 ≤ β:=(R.alloy.B.a.fits.delayed b).le
  have growth:1 ≤ β^d₀:=one_le_pow₀ inc
  have money:0 ≤ M*β^d₀:=mul_nonneg mp (zero_le_one.trans growth)
  have xbound (U:Space):‖X₀ U‖ ≤ oldFee+‖pure U‖:=by
    rw [show X₀ U=rest U+pure U by dsimp only [X₀,pure];ring]
    exact (norm_add_le ..).trans (add_le_add (oldPrice U) (le_refl _))
  have total (U:Space):‖X₀ U‖ ≤ (oldFee+2*cost s M)*β^(d₀*s.val.card):=by
    have raw:=YM.Integration.WilsonOriginalOrdinaryFlatHulls.gross s _ _ (quiet U) money (salary U)
    have base:1+M*β^d₀ ≤ (1+M)*β^d₀:=by rw [add_mul,one_mul];gcongr
    have priced:=pow_le_pow_left₀ (by linarith only [money]) base s.val.card
    rw [mul_pow,←pow_mul] at priced
    apply (xbound U).trans
    rw [add_mul]
    apply add_le_add (le_mul_of_one_le_right op (one_le_pow₀ inc)) (raw.trans _)
    unfold cost
    calc
      _ ≤ 2*((shards J s).card*((1+M)^s.val.card*β^(d₀*s.val.card))):=by gcongr
      _=_:=by ring
  have clean (U:Space)(ok:∀a∈s.val,Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {o a}) U):
      ‖X₀ U‖ ≤ oldFee+change s (M*β^d₀) δ:=by
    apply (xbound U).trans (add_le_add (le_refl oldFee) ?_)
    apply ordinary s _ _ (quiet U) money small
    intro t ht
    exact ⟨(salary U t ht).2,(WilsonOriginalFlatHull.healthy (rows t ht).crop U (ok _ (ht (member t)))).trans (due t ht)⟩
  have softPrice:=WilsonOriginalFlatHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p (d₀*s.val.card) pos late s.val o strength X₀ borel
    (add_nonneg op (show 0 ≤ change s (M*β^d₀) δ by unfold change;apply sum_nonneg;intro t _;positivity))
    (add_nonneg op (show 0 ≤ 2*cost s M by unfold cost;positivity)) total clean ui ib
  have ib':i ≤ b:=(Nat.le_succ i).trans ib
  have payout:hitWidth (Ψ b).p*v₀ ≤ κ:=by
    rw [walk.truep.point]
    exact ((eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (p+d₀*s.val.card) pos)).choose_spec b late).1
  have c0:=((eventually_atTop.mp (WilsonCenteredDividedRoom.original R simple)).choose_spec b divLate).1
  have quote:=toll (Ψ b).p Z w hw s ep dp rp hv div c0 payout
  have posCash:0 ≤ (Poly.toll w s)⁻¹*cash:=by
    apply mul_nonneg (inv_nonneg.mpr (Poly.worth hw s).le)
    dsimp only [cash,WilsonOriginalFlatOccupiedRate.bill,WilsonOriginalFlatOccupiedRate.roof]
    positivity
  have first:0<1+(Poly.toll w s)⁻¹*cash:=by linarith only [posCash]
  have cap:=quote.trans (le_add_of_nonneg_left zero_le_one)
  have hardPrice:=WilsonMeasuredOwnerFlatCourse.order R π Γ Ψ course cut.le S A y q valid payment
    simple way D Q ticket floor ub fixed first cap ui ib' p pos hardLate
  have hardIncome:Integrable H₀ (prior G _):=by
    rw [show H₀=account q (Ψ b) by exact funext fun U=>(field U).symm]
    exact WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course (floor.trans ub) cut.le S A y q valid payment
  have env:Envelope (Ψ b).eval:=(Ψ b).envelope walk.truep.valid
  have softIncome:Integrable R₀ (prior G _):=by
    apply (((env.integrable (prior G _)).norm).mul_const ((oldFee+2*cost s M)*β^(d₀*s.val.card))).mono'
      ((Complex.continuous_ofReal.measurable.comp env.1).mul borel).aestronglyMeasurable
    exact ae_of_all _ (fun U=>by
      change ‖((Ψ b).eval U:ℂ)*X₀ U‖ ≤ ‖(Ψ b).eval U‖*_
      rw [norm_mul,Complex.norm_real];exact mul_le_mul_of_nonneg_left (total U) (norm_nonneg _))
  have split:(fun U=>(A₀.density x U).part s-((Ψ b).eval U:ℂ)*(Poly.pass (I U)).part s)=R₀+H₀:=by
    funext U;dsimp only [R₀,H₀,X₀,Pi.add_apply];ring
  have reg:reading R (N:=N) R₀ i ib'=actualTransport R.family (N:=N) X₀ ib' 1:=by
    dsimp only [R₀];rw [same];exact WilsonThermometerUnitFilingPosterior.weighted R X₀ ib'
  rw [split,WilsonThermometerUnitFilingRaw.add R R₀ H₀ softIncome hardIncome ib',reg,
    WilsonThermometerUnitFilingRaw.ratio R cut.le (Ψ b) same H₀ ib']
  apply (norm_add_le ..).trans (add_le_add softPrice ?_)
  simpa only [field] using hardPrice

end YM.Integration.WilsonOriginalFlatFiledHearing
