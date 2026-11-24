import YM.Integration.WilsonOriginalFlatOccupiedFace
import YM.Integration.WilsonOriginalOrdinaryFlatHulls
import YM.Integration.WilsonThermometerUnitFilingRaw
import YM.Integration.WilsonMeasuredOwnerIntegrable

/-! The regular partition and every occupied hard owner are tested on one
original normalized posterior. The compact Taylor estimate is taken on the
uncut prints, while the actual masked regular register retains its own debit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatGalleryHearing
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
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m  ≤  u)(ub:u  ≤  b)
   (fixed:WilsonSingleHardRadius.first R simple  ≤  u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance b
local notation "Space" => Config G (R.family.side b per)

include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p d₀:ℕ)
    {tol:ℝ}(pos:0<tol)(hardLate:WilsonSingleHardRadius.start R simple p pos ≤ b)
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    (o:V→Site (R.family.side b per))(G₀:Gallery X ι o (Ψ b) J)(x:X)(s:J.Mode)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (p+d₀*s.val.card) pos)).choose  ≤  b)
    (Z:Support (R.family.side b per))(y:Site (R.family.side b per))(center:y∈Z)
    (resident:∀a∈s.val,o a∈Z)(w:V→ℝ)(radii:∀a,0<w a){E hard:ℝ}
    (regular:G₀.E.Paid w (Ψ b).p.B ((Ψ b).p.supportExponent+2) E)
    (forced:G₀.K.Paid w (Ψ b).p.B (Ψ b).p.supportExponent hard)
    {α:ℝ}(strength:(Ψ b).p.supportExponent ≤ α)(L:LinkTube G)(front:Hot J→V)(member:∀t,front t∈t.val.val)
    (print I:Space→Poly J)(neutral:∀U,(I U).part J.quiet=0)
    (borel:Measurable (fun U=>soft G₀ x s U-(Poly.pass (I U)).part s))
    {M δ rent:ℝ}(mp:0 ≤ M)(dp:0 ≤ δ)(rp:0 ≤ rent)
    (salary:∀U (t:Hot J),t.val.val⊆s.val →
      ‖(G₀.E.log x U).part t.val‖ ≤ M*β^d₀ ∧ ‖(I U).part t.val‖ ≤ M*β^d₀)
    (rows:∀(t:Hot J),t.val.val⊆s.val → WilsonOriginalOrdinaryFlatHulls.Row (Ψ b).p L (o (front t))
      (fun U=>(print U).part t.val) (fun U=>(I U).part t.val))
    (due:∀t ht,(rows t ht).price ≤ δ)
    (issued:∀U (t:Hot J),t.val.val⊆s.val → Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {o (front t)}) U →
      ‖(G₀.E.log x U).part t.val-(print U).part t.val‖ ≤ rent)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b) :
    let fare:=WilsonFullFaceSignedHard.fee (Ψ b).p Z w s E hard v₀ κ
    ‖reading R (N:=N) (fun U=>(G₀.density x U).part s-((Ψ b).eval U:ℂ)*(Poly.pass (I U)).part s)
        i ((Nat.le_succ i).trans ib)‖ ≤ 
      change s (M*β^d₀) (rent+δ)+2*cost s M*s.val.card*(4*Real.exp (α+2))*tol/β^p+
        4*(1+max 0 fare)*tol/β^p:=by
  intro fare
  let X₀:Space→ℂ:=fun U=>soft G₀ x s U-(Poly.pass (I U)).part s
  let H:Space→ℂ:=fun U=>(G₀.density x U).part s-((Ψ b).eval U:ℂ)*soft G₀ x s U
  let R₀:Space→ℂ:=fun U=>((Ψ b).eval U:ℂ)*X₀ U
  have walk:=course.1.walk b (floor.trans ub) cut.le
  have same: (Ψ b).eval=(R.family.path.rep N per b).eval := walk.view
  have quiet (U:Space): (G₀.E.log x U).part J.quiet=0 ∧ (I U).part J.quiet=0 :=by
    refine ⟨?_,neutral U⟩
    by_cases h:Summable (fun j=>G₀.E.frame j x U)
    · exact Lamps.quiet_of_hasSum x U h
    rw [Lamps.log,tsum_eq_zero_of_not_summable h]
    rfl
  have inc:1 ≤ β :=(R.alloy.B.a.fits.delayed b).le
  have growth:1 ≤ β^d₀:=one_le_pow₀ inc
  have money:0 ≤ M*β^d₀:=mul_nonneg mp (zero_le_one.trans growth)
  have raw (U:Space):‖X₀ U‖ ≤ 2*cost s (M*β^d₀):=
    YM.Integration.WilsonOriginalOrdinaryFlatHulls.gross s _ _ (quiet U) money (salary U)
  have total (U:Space):‖X₀ U‖ ≤ (2*cost s M)*β^(d₀*s.val.card):=by
    have base:1+M*β^d₀ ≤ (1+M)*β^d₀:=by rw [add_mul,one_mul];gcongr
    have priced:=pow_le_pow_left₀ (by linarith only [money]) base s.val.card
    unfold cost at raw ⊢
    rw [mul_pow,←pow_mul] at priced
    calc
      _ ≤ 2*((shards J s).card*((1+M)^s.val.card*β^(d₀*s.val.card))) := by apply (raw U).trans;gcongr
      _=_:=by ring
  have near (U:Space)(healthy:∀a∈s.val,Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {o a}) U):
      ‖X₀ U‖ ≤ change s (M*β^d₀) (rent+δ):=by
    apply ordinary s _ _ (quiet U) money (add_nonneg rp dp)
    intro t ht
    have clear:=healthy (front t) (ht (member t))
    exact ⟨(salary U t ht).2,(norm_sub_le_norm_sub_add_norm_sub _ ((print U).part t.val) _).trans
      (add_le_add (issued U t ht clear) ((WilsonOriginalFlatHull.healthy (rows t ht).crop U clear).trans (due t ht)))⟩
  have softPrice:=WilsonOriginalFlatHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p (d₀*s.val.card) pos late s.val o strength X₀ borel
    (show 0 ≤ change s (M*β^d₀) (rent+δ) by unfold change;apply sum_nonneg;intro q _;positivity)
    (show 0 ≤ 2*cost s M by unfold cost;positivity) total near ui ib
  obtain ⟨keeper⟩:=WilsonCenteredCourseKeeper.original R course b (floor.trans ub) cut
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec b capture
  rw [←walk.truep.point] at room
  obtain ⟨q,valid,paid,field⟩:=WilsonOriginalFlatOccupiedFace.owned (F:=F) G₀ x s A Z y center resident
    keeper w radii walk.truep.valid hv room div regular forced
  have hardIncome:Integrable H (prior G _) :=by
    have eq:account q (Ψ b)=H:=funext field
    rw [←eq]
    exact WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course (floor.trans ub) cut.le S A y q valid paid
  have env:Envelope (Ψ b).eval:=(Ψ b).envelope walk.truep.valid
  have softIncome:Integrable R₀ (prior G _) :=by
    apply (((env.integrable (prior G _)).norm).mul_const (2*cost s (M*β^d₀))).mono'
      ((Complex.continuous_ofReal.measurable.comp env.1).mul borel).aestronglyMeasurable
    exact ae_of_all _ (fun U=>by
      change ‖((Ψ b).eval U:ℂ)*X₀ U‖ ≤ ‖(Ψ b).eval U‖*(2*cost s (M*β^d₀))
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (raw U) (norm_nonneg _))
  have split:(fun U=>(G₀.density x U).part s-((Ψ b).eval U:ℂ)*(Poly.pass (I U)).part s)=R₀+H:=by
    funext U;dsimp only [R₀,H,X₀,Pi.add_apply];ring
  have ib':i ≤ b:=(Nat.le_succ i).trans ib
  have r0:reading R (N:=N) R₀ i ib'=actualTransport R.family (N:=N) X₀ ib' 1:=by
    dsimp only [R₀];rw [same];exact WilsonThermometerUnitFilingPosterior.weighted R X₀ ib'
  have hardPrice:=WilsonOriginalFlatOccupiedFace.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p pos hardLate o G₀ x s Z y center resident w radii regular forced ui ib'
  rw [split,WilsonThermometerUnitFilingRaw.add R R₀ H softIncome hardIncome ib']
  apply (norm_add_le ..).trans
  rw [r0,WilsonThermometerUnitFilingRaw.ratio R cut.le (Ψ b) same H ib']
  exact add_le_add softPrice hardPrice

end YM.Integration.WilsonOriginalFlatGalleryHearing
