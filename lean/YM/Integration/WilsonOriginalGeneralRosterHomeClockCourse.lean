import YM.Integration.WilsonOriginalGeneralRosterHomeStops
import YM.Integration.WilsonOriginalAllOrderCourse

/-! The reporter band and the independent stopping rule are bought from
the same nested original course before any stock test is placed. The
corresponding world may be the initializer already holding the trial rows. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomeClockCourse
open Function Filter Set Lattice RG Wilson Source Labels Extraction Table Spec PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato Climb Next.Rank Pert.Asymptotics
open WilsonLimitConstruction GapsContact GapsContact.Ascent RG RG.Supply
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPositionProgramReporterBand (Band)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{W₀:Campaign.Pillars R campaign}
    (p:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W₀)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (world:XSpace.Run){index:ℕ}(positive:0 < index)(ratio:world.ratio=(3:ℕ)^index)(stage before depth:ℕ):
    let older:=max (R.family.ref 0) before
    ∃run:Band R world (stage+1),∃stop:WilsonIndependentCapturedPages.Stop R world run older (depth+1),
    ∀(I:Type)[Fintype I][Nonempty I](D T:ℕ)(δ:ℝ)(ask floor h reserve:ℕ)
      (d:I→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
      (arity:I→ℕ)(φ:∀i,Test (arity i))(house:I→ℝ)(hp:∀i,0<house i),
      type_of% (WilsonOriginalGeneralRosterHomeStops.original F simple bliss slow ready run stop
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (le_max_left ..) ask floor h reserve d books arity φ house hp):=by
  intro older
  obtain ⟨run⟩:=WilsonPositionProgramReporterBand.original R world simple p.nested positive ratio slow.2 (stage+1)
  obtain ⟨stop⟩:=WilsonIndependentCapturedPages.original R world simple slow run older (depth+1)
  exact ⟨run,stop,fun _ _ _ _ _ _ ask floor h reserve d books arity φ house hp=>
    WilsonOriginalGeneralRosterHomeStops.original F simple bliss slow ready run stop (Nat.zero_lt_succ _)
      (Nat.zero_lt_succ _) (le_max_left ..) ask floor h reserve d books arity φ house hp⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeClockCourse
end
