import YM.Integration.WilsonOriginalPublicNodalStandardCells
import YM.Integration.WilsonMovingForkThermalReversion

/-! Both genuine reported programmes on the filed finite cell roster, expressed in the appointed common clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkAppointedReportedCells
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Source Labels PertExtension RegulatorIR.Epoch RegulatorIR.Epoch.League
open XSpace Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Momentum
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates Next.Foundations
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open scoped Classical ENNReal NNReal BigOperators PowerSeries
variable {G:Gauge}{H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(P:Master H)(chart:ChartRatio G)(V:XSpace.Run)
    (e h k tier extra:ℕ)(p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)
variable (Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(col:G.ColorIndex)
    (B:WilsonIndependentEvenPassport.Menu P chart R.family.path.levels.clock.kernel V e h k tier extra)
    (late:5≤tier){X:Type}(m j:X → ℕ)(w:X → ℕ → ℕ)
    (blocks:∀x t,(R.family.S.block (m x+t)).val=V.ratio^(w x t))(r:X → ℕ)(ap:X → ℝ)(pos:∀x,0≤ap x)




open RegulatorIR.Halo RegulatorIR.Prim RegulatorIR.Profiles RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Cluster RegulatorIR.Budget RegulatorIR.Motion XSpace.Rose XSpace.Cirrus
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalCommonRaw (value raw fee prior)
open WilsonOriginalPublicNodalTwinOrbit (stride lift)
open WilsonOriginalPublicNodalHelperElection (TwoNotebooks)
open WilsonOriginalPublicNodalPhysicalHelper (period sample)
variable (T:TwoNotebooks R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos)
    (i:X → ℕ)(H:ℝ)
local notation "A" => WilsonOriginalPublicNodalHelperElection.groupedCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T
local notation "C" => WilsonOriginalPublicNodalHelperElection.physicalCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H


open WilsonIndependentExactPlate (Requests M S)
open WilsonIndependentRawRosterOrbit (report)
local notation "S₀" => S V B.a B.positive tier (le_trans (by decide:4 ≤ 5) late)
local notation "D₀" => WilsonOriginalPublicNodalHelperCircuit.circuit V (physical j w) r B.a tier B.positive (le_trans (by decide:4 ≤ 5) late)
local notation "Y₀" => Oracle.books R.family.path.levels.clock.kernel
variable (F₀:Tent (M V B.a))(book:Notebook (S V B.a B.positive tier (le_trans (by decide:4 ≤ 5) late)) (Oracle.books R.family.path.levels.clock.kernel) G Z col (Rocket.native _) F₀ p)


open WilsonThermometerPositionTunedSlope (Columns)
open WilsonIndependentPublicReportComplex (row)
open WilsonOriginalPublicNodalStandardCells (Allowance sampled earlier bill)
variable {I:Type}[Fintype I](W:Initialize G)(σ:I → Bool)(d:I → ℕ)(arms:Composite I)
    (mesh:X → ℝ)(hm:∀x,0 < mesh x)(lay:X → Fin 2 → Cover)(origin:X → Room)
    (base:X → Cover)(sites:X → I → Cover)(gs:Choice (length (physical j w) r B.a))(ps:Choice j)
    (request:X → Requests B.a)(at₀:X → Choice (M V B.a))
    (residue:∀x,(request x).val%B.a=r x)(ages:∀x,(at₀ x).age (request x)=gs.age x)
    (enough:∀x,r x ≤ physical j w x)


local notation "source" => sampled R P chart V e h k tier extra Z B late F₀ W σ d arms sites request at₀
local notation "sink" => earlier R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H W σ d arms sites ps
local notation "charge" => bill R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H gs ps
include book hm lay origin residue ages enough in
theorem original
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x):∃L:Columns R d → ℕ → Allowance,
    ∀(D q:ℕ),q≤p → ∀(Cell:Type)[Fintype Cell](ear:Cell → Page ps.after.spans)(ν:Cell → ℂ)
      (v:Cell → ∀t,(R.family.labels.level (d t)).Coeff)(age:Cell → Page j),
      let K:=fun z=>F₀ (WilsonIndependentExactPlate.report V B.a (request (ear z).bindW))
      let c:=fun z (a:Columns R d)=>∏t,v z t (a t)
      ‖∑z,ν z*(PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (K z) D
           (∑a,PowerSeries.C (c z a)*source a (ear z).bindW))-
         WilsonMovingForkThermalReversion.inClock (K z) (T.F (age z)) D D q
           (fun l => PowerSeries.coeff l (WilsonIndependentPublicReportComplex.apply (T.F (age z)) D
             (∑a,PowerSeries.C (c z a)*sink a (ear z)))))‖≤
        ∑z,‖ν z‖*(∑a,‖c z a‖*∑l∈Finset.range (q+1),charge (L a l) (ear z).bindW*‖row (K z) D q l‖):=by
  obtain ⟨L,paid⟩:=WilsonOriginalPublicNodalStandardCells.original R P chart V e h k tier extra p b u
    γ Z col B late m j w blocks r ap pos T i H F₀ book W σ d arms mesh hm lay origin base sites gs ps
    request at₀ residue ages enough room field funded
  refine ⟨L,?_⟩
  intro D q hq Cell _ ear ν v age K c
  have rewriteClock (a b:RegulatorIR.Profiles.Feeds)(F:PowerSeries ℂ) :
      WilsonMovingForkThermalReversion.inClock a b D D q
        (fun l => PowerSeries.coeff l (WilsonIndependentPublicReportComplex.apply b D F)) =
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply a D F) := by
    let f := fun j => PowerSeries.coeff j F
    have same : PowerSeries.mk f = F := by ext j; simp [f]
    simpa only [WilsonMovingForkCommonRawClocks.heard,same] using
      WilsonMovingForkThermalReversion.transfer a b D D q f
  simp_rw [rewriteClock]
  exact paid D q hq Cell ear ν v

end YM.Integration.WilsonMovingForkAppointedReportedCells
end
