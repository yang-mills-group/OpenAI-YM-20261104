import YM.Integration.WilsonOriginalTwoFlatWithdrawal
import YM.Integration.WilsonOriginalPaidFlatHalos

/-! One actual occupied mixed face against its independently printed ordinary
value, through the same physical Haar history, at either older flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatDated
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor
open WilsonThermometerUnitFilingCoarse (reading)
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Source Labels OPE.Therm
open WilsonReceivedQuietCrownOwner
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b t:ℕ}
variable {V:Type} [DecidableEq V] [Fintype V] {marks:Marker.Census V}
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (ticket:TicketP R.alloy R.kit D Q)
  {X I:Type} [Countable I] [Nonempty X] (o:V → Site (R.family.side t per))
  (A:Gallery X I o (Ψ t) marks)(w:V → ℝ)(wp:∀v,0<w v)

variable (simple:G.Simple){u i:ℕ}(floor:m ≤ u)(ub:u ≤ b)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    (ui:u ≤ i)(ib:i ≤ b)(bt:b<t)(top:t ≤ N)
    (Z₀:Support (R.family.side b per))(center:Site (R.family.side b per))(home:center∈Z₀)
local notation "κc" => LocalComparison.forcedDivisor R.family b
local notation "βc" => R.alloy.B.a.clock.hatBeta b

include course ticket way wp simple floor ub fixed capture ui ib bt top home in
theorem original {load:ℕ}
    (stage:∀k,b ≤ k → load ≤ R.alloy.B.a.clock.J k)(load_ok:∀s:marks.Mode,s.val.card ≤ load)
    (cap:∀k,b ≤ k → LocalComparison.forcedDivisor R.family k ≤ 1)
    (s:marks.Mode)(anchors:∀v∈s.val,sites R o bt.le v∈Z₀)
    (n:ℕ)(np:0<n)(size:s.val.card ≤ n)
    (tiny:WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t) ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (hard:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t))(x:X)

    (nonbare:t<N)(printed:Config G (R.family.side t per) → ℂ)
    (borel:Measurable printed){B e:ℝ}(bp:0≤B)(ep:0≤e)
    (gross:∀U,‖(Poly.pass (A.E.log x U)).part s-printed U‖ ≤ B)
    (healthy:∀U,(∀a∈s.val,Healthy (Ψ t).p.threshold (halo (Ψ t).p.B {o a}) U) →
      ‖(Poly.pass (A.E.log x U)).part s-printed U‖ ≤ e):
    let money:=Poly.toll (wallet R w bt.le) s
    let roof:=((shards marks s).card:ℝ)+4*(money+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z₀ 1 s.val.card)*βc*κc
    let term:=s.val.card*(4*hitWidth (Ψ t).p*Real.exp ((Ψ t).p.supportExponent+2)*
      R.alloy.B.a.clock.hatBeta t*R.alloy.B.a.clock.forcedAllowance t)
    money*‖reading R (N:=N) (fun U=>(A.density x U).part s) i (ib.trans bt.le)-
      reading R (N:=N) (fun U=>((Ψ t).eval U:ℂ)*printed U) i (ib.trans bt.le)‖ ≤
      WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t)*price n*roof+
      money*(e+B*term):=by
  intro money roof term
  let F:=fun U=>(Poly.pass (A.E.log x U)).part s
  let it:=ib.trans bt.le
  let E:=F-printed
  have canon:(Ψ t).eval=(R.family.path.rep N per t).eval:=(course.1.walk t ((floor.trans ub).trans bt.le) top).view
  have canon':(Ψ i).eval=(R.family.path.rep N per i).eval:=(course.1.walk i (floor.trans ui) (it.trans top)).view
  let pay₁:=WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t)
  have kp:0<LocalComparison.forcedDivisor R.family t:=Real.sqrt_pos.2 (Real.exp_pos _)
  have fund:=WilsonOriginalOccupiedWallet.enrolled A w wp n np _ kp tiny hard
  have law:=(course.1.walk t ((floor.trans ub).trans bt.le) top).truep.valid
  have pack (z:ℂ)(hz:z∈nodes n ((pay₁⁻¹:ℝ):ℂ)):(gallery z A).Pays w (Ψ t).p.supportExponent 1 1:=⟨regular,fund z hz⟩
  have live (z:ℂ)(hz:z∈nodes n ((pay₁⁻¹:ℝ):ℂ)):=QuadraticLocal.Tariff.integrable marks o w wp (gallery z A) x (pack z hz) (Ψ t).p.exponent_pos.le law
  let lag:=fun U=>((Ψ t).eval U:ℂ) • Poly.pass (A.E.log x U)
  have erase:(gallery 0 A).density x=lag:=funext fun U=>WilsonOriginalOccupiedWallet.origin A x U w wp (fund 0 (by simp [nodes]))
  have keep:(gallery 1 A).density x=A.density x:=funext (WilsonOriginalOccupiedSource.one A x)
  have q₀:=live 0 (by simp [nodes]); rw [erase] at q₀
  have q₁:=live 1 (by simp [nodes]); rw [keep] at q₁
  have readpart (Z:Config G (R.family.side t per) → Poly marks)(eligible:Integrable Z (prior G _)):
      reading R (N:=N) (fun U=>(Z U).part s) i it=
      (((Ψ i).eval 1:ℂ)⁻¹)*(gust R.family.path N per t Z i it 1).part s:=by
    unfold WilsonThermometerUnitFilingCoarse.reading
    rw [←WilsonOriginalOccupiedTransport.projected R Z eligible s it,canon']
  have hpay:=WilsonOriginalTwoFlatWithdrawal.original R way D Q π Γ Ψ course ticket o A w wp
    simple floor ub fixed capture ui ib bt top Z₀ center home stage load_ok cap s anchors n np size tiny regular hard x
  let lhs:=reading R (N:=N) (fun U=>(A.density x U).part s) i it
  let soft:=reading R (N:=N) (fun U=>(lag U).part s) i it
  let rhs:=reading R (N:=N) (fun U=>((Ψ t).eval U:ℂ)*printed U) i it
  have hardprice:money*‖lhs-soft‖≤pay₁*price n*roof:=by
    dsimp only [lhs,soft];rw [readpart _ q₁,readpart _ q₀,←mul_sub];exact hpay
  have mf:Measurable F:=WilsonOriginalTwoFlatRegular.measurable A.E x s
  have fp:=Poly.worth wp s
  let C:=((shards marks s).card:ℝ)/Poly.toll w s
  have fcap (U):‖F U‖≤C:=(le_div_iff₀ fp).2 ((mul_comm ..).trans_le
    (WilsonOriginalTwoFlatRegular.masked (Ψ t) A.E wp regular x s U))
  have icap (U):‖printed U‖≤C+B:=by
    calc _=‖F U-(F U-printed U)‖:=by rw [sub_sub_cancel]
         _≤‖F U‖+‖F U-printed U‖:=norm_sub_le .. 
         _≤_:=add_le_add (fcap U) (gross U)
  have step:i+1≤t:=Nat.succ_le_of_lt (lt_of_le_of_lt ib bt)
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per step 1
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R step top 1
  letI:IsProbabilityMeasure (scene R.family.path N per t):=probability R.makes.wilson top
  have intF (μ:Measure _) [IsProbabilityMeasure μ]:Integrable F μ:=
    Integrable.of_bound mf.aestronglyMeasurable _ (ae_of_all _ fcap)
  have intI (μ:Measure _) [IsProbabilityMeasure μ]:Integrable printed μ:=
    Integrable.of_bound borel.aestronglyMeasurable _ (ae_of_all _ icap)
  have paid:=WilsonOriginalPaidFlatHalos.original R π Γ Ψ course nonbare (R.family.localSection 0)
    R.family.params simple way D Q ticket floor (ub.trans bt.le) fixed (capture.trans bt.le)
    s.val o E (mf.sub borel) ep bp gross healthy ui step
  have softprice:‖soft-rhs‖≤e+B*term:=by
    have hs:soft=actualTransport R.family (N:=N) F it 1:=by
      change reading R (N:=N) (fun U=>((Ψ t).eval U:ℂ)*F U) i it=_
      rw [canon,WilsonThermometerUnitFilingPosterior.weighted]
    have hi:rhs=actualTransport R.family (N:=N) printed it 1:=by
      dsimp only [rhs];rw [canon,WilsonThermometerUnitFilingPosterior.weighted]
    rw [hs,hi,WilsonOriginalFailedHaloPosterior.flat R step top F (intF _),
      WilsonOriginalFailedHaloPosterior.flat R step top printed (intI _),←integral_sub (intF μ) (intI μ)]
    rw [WilsonOriginalFailedHaloPosterior.flat R step top E ((intF _).sub (intI _))] at paid
    exact paid
  have mp : 0 ≤ money:=(Poly.worth (positive R w wp bt.le) s).le
  change money*‖lhs-rhs‖≤_
  calc _ ≤ money*(‖lhs-soft‖+‖soft-rhs‖):=mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub ..) mp
       _ = _ + _:=mul_add ..
       _ ≤ _:=add_le_add hardprice (mul_le_mul_of_nonneg_left softprice mp)

end YM.Integration.WilsonOriginalTwoFlatDated
end
