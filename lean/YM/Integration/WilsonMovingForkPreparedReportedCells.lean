import YM.Integration.WilsonOriginalPublicNodalStandardCells
import YM.Integration.WilsonMovingForkAppointedReportedCells

/-! Both genuine reported programmes on the filed finite cell roster, expressed in the appointed common clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkPreparedReportedCells
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
open PowerSeries Finset

/-- Price the raw convolution before changing either reporting clock. -/
theorem convolution {Addr : Type*} [Fintype Addr] (c f g : Addr → PowerSeries ℂ) (l : ℕ)
    (price : Addr → ℕ → ℝ) (paid : ∀ a j, j ≤ l → ‖coeff j (f a) - coeff j (g a)‖ ≤ price a j) :
    ‖coeff l (∑a, c a * f a) - coeff l (∑a, c a * g a)‖ ≤
      ∑a, ∑jk∈antidiagonal l, ‖coeff jk.1 (c a)‖ * price a jk.2 := by
  rw [map_sum,map_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [coeff_mul,coeff_mul,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk hjk
  rw [←mul_sub,norm_mul]
  have eq : jk.1 + jk.2 = l := by simpa using hjk
  exact mul_le_mul_of_nonneg_left (paid a jk.2 (by omega)) (norm_nonneg _)

include book hm lay origin residue ages enough in
/-- Two separately funded notebooks with the genuine bare group stencil and a
full series as its amplitude at each placement. -/
theorem original
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x):∃L:Columns R d → ℕ → Allowance,
    ∀(D q:ℕ),q≤p → ∀(Cell:Type)[Fintype Cell](ear:Cell → Page ps.after.spans)(ν:Cell → ℂ)
      (c:Cell → Columns R d → PowerSeries ℂ)(age:Cell → Page j),
      let K:=fun z=>F₀ (WilsonIndependentExactPlate.report V B.a (request (ear z).bindW))
      ‖∑z,ν z*(coeff q (WilsonIndependentPublicReportComplex.apply (K z) D
           (∑a,c z a*source a (ear z).bindW))-
         WilsonMovingForkThermalReversion.inClock (K z) (T.F (age z)) D D q
           (fun l => coeff l (WilsonIndependentPublicReportComplex.apply (T.F (age z)) D
             (∑a,c z a*sink a (ear z)))))‖≤
        ∑z,‖ν z‖*(∑l∈Finset.range (q+1),(∑a,∑jk∈antidiagonal l,
          ‖coeff jk.1 (c z a)‖*charge (L a jk.2) (ear z).bindW)*‖row (K z) D q l‖):=by
  classical
  let issued:=WilsonOriginalPublicNodalStandardCells.entry R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H F₀ book
    W σ d arms mesh hm lay origin base sites gs ps request at₀ residue ages enough room field funded
  choose L stock using issued
  refine ⟨L,?_⟩
  intro D q hq Cell _ ear ν c age K
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let f:=∑a,c z a*source a (ear z).bindW
  let g:=∑a,c z a*sink a (ear z)
  have recoverClock :
      WilsonMovingForkThermalReversion.inClock (K z) (T.F (age z)) D D q
        (fun l => coeff l (WilsonIndependentPublicReportComplex.apply (T.F (age z)) D g)) =
        coeff q (WilsonIndependentPublicReportComplex.apply (K z) D g) := by
    let a:=fun j=>coeff j g
    have same:PowerSeries.mk a = g := by ext j; simp [a]
    simpa only [WilsonMovingForkCommonRawClocks.heard,same] using
      WilsonMovingForkThermalReversion.transfer (K z) (T.F (age z)) D D q a
  change ‖coeff q (WilsonIndependentPublicReportComplex.apply (K z) D f)-
      WilsonMovingForkThermalReversion.inClock (K z) (T.F (age z)) D D q
        (fun l=>coeff l (WilsonIndependentPublicReportComplex.apply (T.F (age z)) D g))‖≤_
  rw [recoverClock,WilsonIndependentPublicReportComplex.difference]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  have lh : l ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  rw [norm_mul,Complex.norm_real]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply convolution (c z) (fun a=>source a (ear z).bindW) (fun a=>sink a (ear z)) l
    (fun a t=>charge (L a t) (ear z).bindW)
  intro a x hx
  have hxp := (hx.trans lh).trans hq
  simpa only [min_eq_left hxp] using stock a x (ear z)

end YM.Integration.WilsonMovingForkPreparedReportedCells
end
