import YM.Integration.WilsonPointChildCenteredSeat
import YM.Integration.WilsonOlderFreshPointChart

/-! The independently seated cover source realizes an arbitrary original
smooth sold film on its actual digit sequence and every auxiliary torus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedRegisteredSeed
open Function Filter Finset Lattice Wilson RG Laurent PowerSeries
open FormalBulk08 Flat Reef Jets Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel.Mark
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNamedBasis WilsonCoeffUV.Wheel
open scoped Classical Topology BigOperators ContDiff
variable {D:ℕ} {G:Gauge}

/-- The submitted smooth representative on the half-cell keeps the original test norm. -/
theorem film (f:Studio D):∃p:Scroll D, physical p=f ∧ ‖page D p‖≤‖f‖:=by
  obtain ⟨Y,rfl⟩:=Dawn.portrayed D f
  refine ⟨scroll Y,physical_scroll Y,vote_cap _ (norm_nonneg _) ?_⟩
  intro b c
  let X:Annex.Deck:=⟨(PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm c.val,
    Annex.cube_test.mpr fun i=>by
      change |c.val i|≤1/2
      simpa [one_div,Real.norm_eq_abs] using (norm_le_pi_norm c.val i).trans (c_norm c)⟩
  let y:=Annex.embark X
  have eq:(physical (scroll Y)).val b y=(page D (scroll Y)).val b c:=by
    change iteratedFDeriv ℝ b.1.val ((scroll Y).val ∘ coordinates) y.val (basis ∘ b.2)=
      iteratedFDeriv ℝ b.1.val (scroll Y).val c.val (dot ∘ b.2)
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right coordinates (scribble (scroll Y) le_rfl) _
      (Nat.cast_le.mpr (Nat.le_of_lt_succ b.1.isLt)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have yc:coordinates y.val=c.val := (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).apply_symm_apply _
    simp only [Function.comp_def,WilsonPointChildTestCoordinates.axis,yc]
  rw [←eq,physical_scroll]
  exact Dawn.le_panel _ _ _

variable {ι:Type}(R:Run G)(simple:G.Simple)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)

include o simple paid tags in
theorem original (h k:ι→ℕ)(depth:∀s,k s<h s)(u:ι→G.ColorIndex)
    (N j:ℕ)(live:j≤N)(up:∀s,k s≤R.family.path.levels.clock.J j)
    (digit:ι→∀i,Site (R.family.S.block i))(v:∀s,Letter (R.family.labels.level (k s)))
    (films:∀s,Studio (h s)):
    ∃V:Case h,(∀s,‖V s‖≤‖films s‖) ∧ ∀s,
      let X:=WilsonPointChildCenteredFunctional.issue R (u s) (k s) h s (depth s) (digit s) N j (v s)
      let Y:Pot G:=fun e r x=>touch V {s} (X.2 e r x)
      Y=WilsonOlderFreshPointGauge.field R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s) ∧
      ∀(n:Side)(home:Site n),WilsonOriginalPlacedPrimerInk.filed (k s) Y n home =
        WilsonOlderFreshPointChart.chart R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s) n home:=by
  choose p agrees norm using fun s=>film (films s)
  let V:Case h:=fun s=>page (h s) (p s)
  refine ⟨V,norm,?_⟩
  intro s X Y
  have law:=WilsonPointChildCenteredJet.original R (routes R) (u s) (depth s) (digit s) N j (v s) (p s)
  rw [agrees s] at law
  have eq:Y=WilsonOlderFreshPointGauge.field R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s):=by
    funext e r x
    exact (WilsonPointChildCenteredFunctional.original R (u s) (k s) h s (depth s) (digit s) o
      simple price paid tags N j live (up s) (v s) e r x V).trans
      (congrArg (fun t:Pot G=>t e r x) law.symm)
  exact ⟨eq,fun n home=>congrArg (fun t:Pot G=>WilsonOriginalPlacedPrimerInk.filed (k s) t n home) eq⟩

end YM.Integration.WilsonCapturedRegisteredSeed
