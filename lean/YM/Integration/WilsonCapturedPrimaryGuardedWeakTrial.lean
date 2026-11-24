import YM.Integration.WilsonCapturedPrimarySeparatedTiles
import YM.Integration.WilsonOriginalMicroscopicGuardedTrial

/-! Guard add-back on the actual clockface. The physical period and cutoff
are common to the guarded canonical section and its full printed section. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryGuardedWeakTrial
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport
open WilsonCapturedPrimaryWeakTileColumn RG17 Next.Rank.Spindle
open WilsonOriginalMicroscopicGuardedTrial
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "fp" => (Ψ b).p
local notation "Z" => Site (R.family.side b per)

include course cut way ticket floor ub fixed S A in
theorem original
    (columns:∀ᶠ j in atTop,(R.family.path.levels.params j).columns ≤ R.family.path.levels.clock.hatBeta j)
    (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p positive)).choose ≤ b)
    (grades:Fin 3→ℕ)(o:Fin 3→Z)(v:∀a:Fin 3,R.family.label (grades a))(s:Finset (Fin 3))
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b)(D₄:ClockFace R 4 i N per)
    (stage:(eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
      (WilsonOriginalClockFacePosterior.original R simple))).choose ≤ i):
    let earlier:=(Nat.le_succ i).trans ib
    let rawFace:=face (raw R grades N per b o v) s
    let guardedFace:=face (guarded R grades N per b o v) s
    let full:=actualTransport R.family (N:=N) rawFace earlier
    let own:=actualTransport R.family (N:=N) guardedFace earlier
    let rent:=2*(∏a∈s, cap R grades N per b v a)
    let hits:=footprint R grades per b o s
    let failed:=rent*(hits.card:ℝ)*(4*Real.exp ((fp).supportExponent+2))*tol/β^p
    (∀ a U,(((R.family.path.rep N per b).eval U:ℝ):ℂ) * guarded R grades N per b o v a U =
      WilsonPositionProgramOriginalBlockedTrial.numerator R (grades a) N per b (o a) (v a) U) ∧
    (∀α,‖full (node R D₄ α)-own (node R D₄ α)‖ ≤ 2*failed) ∧
    Next.Rank.Spindle.paid R.family 4 i N per (column R D₄ full-column R D₄ own)
      ≤ 44*(R.family.path.levels.clock.hatBeta i)^27*(2*failed):=by
  intro earlier rawFace guardedFace full own rent hits failed
  let Y:=gap R grades N per b o v s
  obtain ⟨borel,range,away,_⟩:=occupied R grades N per b o v s
  have same:(Ψ b).p=(R.family.path.rep N per b).p:=
    (course.1.walk b (floor.trans ub) cut.le).truep.point.trans (R.makes.wilson.represents N per b cut.le).vac.symm
  have clear:∀U,(∀a∈hits,Healthy (fp).threshold (halo (fp).B {a}) U)→‖Y U‖ ≤ 0:=by
    intro U sound
    rw [show Y U=0 from away U (by
      rintro ⟨a,ha,bad⟩
      have inHalo:a∈halo (fp).B {a}:=halo_spec.mpr ⟨a,by simp,by simp⟩
      rw [←same] at bad
      exact Finset.disjoint_left.mp (sound a ha) inHalo bad),norm_zero]
  have rp:0 ≤ rent:=(norm_nonneg (Y 1)).trans (range 1)
  have bp:0 ≤ β:=zero_le_one.trans (R.family.path.levels.fits.delayed b).le
  have fp₀:0 ≤ failed:=by dsimp only [failed];positivity
  obtain ⟨read,tilt⟩:=(eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
    (WilsonOriginalClockFacePosterior.original R simple))).choose_spec i stage
  have live:= (Nat.lt_of_succ_le ib).trans cut
  have absolute (α):‖actualTransport R.family (N:=N) Y earlier (node R D₄ α)‖ ≤ 2*failed:=by
    have h:=WilsonOriginalDecoderHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed capture
      p 0 positive (by simpa only [Nat.add_zero] using late) hits id le_rfl Y borel (e:=0) (B:=rent)
      le_rfl rp (by simpa only [pow_zero,mul_one] using range) clear ui ib (node R D₄ α)
    rw [zero_add] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (tilt live D₄ α) fp₀).trans_eq (mul_comm _ _))
  have each:=unary R grades N per b o v
  have measRaw:Measurable rawFace:=Finset.measurable_prod _ (fun a _=>(each a).2.1)
  have measGuard:Measurable guardedFace:=Finset.measurable_prod _ (fun a _=>(each a).1)
  let B:=∏a∈s,cap R grades N per b v a
  have bounded (F:Fin 3 → Config G (R.family.side b per)→ℂ)(U)
      (bought:∀a,‖F a U‖ ≤ cap R grades N per b v a): ‖face F s U‖ ≤ B:=by
    rw [face,norm_prod]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>bought a)
  have br:∀U,‖rawFace U‖ ≤ B:=fun U=>bounded _ U (fun a=>((each a).2.2 U).2)
  have bg:∀U,‖guardedFace U‖ ≤ B:=fun U=>bounded _ U (fun a=>((each a).2.2 U).1)
  let ν:=scene R.family.path N per b
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson cut.le
  have integrable (μ:Measure (Config G (R.family.side b per))) [IsFiniteMeasure μ]
      (f:Config G (R.family.side b per)→ℂ) (hm:Measurable f) (hb:∀U,‖f U‖ ≤ B): Integrable f μ:=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hb)
  have balance (U:Config G (R.family.side i per)):full U-own U=actualTransport R.family (N:=N) Y earlier U:=by
    let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib U
    letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R ib cut.le U
    have actual (f:Config G (R.family.side b per)→ℂ) (ints:Integrable f ν):
        actualTransport R.family (N:=N) f earlier U=∫V,f V ∂μ:=
      (congrFun (WilsonSeparatedOriginalPosteriorTransport.realized (C:=R.family) (N:=N) (p:=per)
        R.makes cut.le earlier f ints) U).symm.trans (WilsonMacroscopicRichFlatPosteriorLaw.reading R ib cut.le U f ints)
    change actualTransport R.family (N:=N) rawFace earlier U-actualTransport R.family (N:=N) guardedFace earlier U=_
    have imr:=integrable ν rawFace measRaw br
    have img:=integrable ν guardedFace measGuard bg
    rw [actual _ imr,actual _ img,actual Y (imr.sub img)]
    exact (integral_sub (integrable μ rawFace measRaw br) (integrable μ guardedFace measGuard bg)).symm
  have nodes (α):‖full (node R D₄ α)-own (node R D₄ α)‖ ≤ 2*failed:=by
    rw [balance];exact absolute α
  exact ⟨fun a U=>(source R grades N per b o v cut.le a U).1,nodes,read live.le D₄ full own _ nodes⟩
end YM.Integration.WilsonCapturedPrimaryGuardedWeakTrial
end
