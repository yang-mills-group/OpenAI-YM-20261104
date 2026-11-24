import YM.Integration.WilsonIndependentRawPhysicalFaces

/-! Period allowance for the measured finite physical figure on its own sites,
with the fitted coefficients restored only after the orbit estimates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentReportedPhysicalTable
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open RegulatorIR.Motion XSpace.Cirrus RegulatorIR.Clocks WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonIndependentRawPhysicalFaces (ordered entered survey weight)
open WilsonThermometerPositionTunedSlope (Columns)
open scoped Classical ENNReal NNReal BigOperators PowerSeries
theorem linear {I:Type}[Fintype I](K:Feeds)(D q:ℕ)(c:I → ℂ)(A:I → PowerSeries ℂ):
    PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D (∑i,PowerSeries.C (c i)*A i))=
      ∑i,c i*PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply K D (A i)):=by
  rw [WilsonIndependentPublicReportComplex.coefficients]
  simp only [map_sum,PowerSeries.coeff_C_mul,Finset.sum_mul,WilsonIndependentPublicReportComplex.coefficients,
    Finset.mul_sum,←mul_assoc]
  exact Finset.sum_comm

variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j:ℕ)(Y:Program K)(branches:∀p:Patch,p.Branches K G)(p b u extra:ℕ)
    (col:G.ColorIndex)(late:4 ≤ j)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)

theorem original (good:G.Simple)(paid:WilsonIndependentTwoMomentGrant.Accounts P chart K V e h k j Y branches
    p b u (3/4) extra col late B)(ap:Requests B.a → ℝ)(positive:∀w,0 ≤ ap w)(F:Tent (M V B.a))
    (book:Notebook (S V B.a B.positive j late) Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) F p)
    (orbit:WilsonIndependentPublicRosterBook.Priced R W K Y branches V B.a j B.positive late p (3/4) ap F)
    {n:ℕ}(d:Fin n → ℕ)(mask:Finset (Fin n))[Nonempty mask]
    (X:Requests B.a → Sample n)(ray:Fin 2 → Fin n)(x:Requests B.a → Room)(c₀:ℝ)
    (same:∀w,(X w).F=V.step w.val)
    (reach:∀w,∑i:mask,dist (x w) (slide 1 ((X w).layout i)) ≤ ap w)
    (clear:0<c₀)(safe:((S V B.a B.positive j late).dialect Y G branches (sheet F)).cushion c₀ x)
    (q:ℕ)(hq:q ≤ p)(D:ℕ)(band:ℝ)(hband:0<band)
    (sq:∀w,(Real.log (1+ap w))^2 ≤ band*Real.log ((V.step w.val).p.side.val:ℝ)):
    let C:=S V B.a B.positive j late
    let δ:mask → ℕ:=fun i=>d i
    let site:Requests B.a → mask → Cover:=fun w i=>(X w).layout i
    let field(a:Columns R δ)(w:Requests B.a):PowerSeries ℂ:=PowerSeries.mk fun i=>(note
      ((WilsonIndependentRawRosterOrbit.report R W (fun _=>false) δ a ordered
        (C.payroll Y G branches (sheet F)) site).main (Page.finallyW (M V B.a) w) i 0):ℂ)
    ∃A:ℝ,0 ≤ A ∧ ∃l:ℕ,∀ (v:(w:Requests B.a) → (i:Fin n) → (R.family.labels.level (d i)).Coeff)
      (w:Requests B.a),
      let scale:=F (WilsonIndependentExactPlate.report V B.a w)
      let μ:ℝ:=(V.step w.val).p.side.val
      let c:=weight R d (v w) mask
      ‖PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D
        (WilsonOriginalPublicPivotReflected.board R W d (v w) (X w) mask))-
        PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply scale D
          (∑a:Columns R δ,PowerSeries.C (c a)*field a w))‖ ≤
        (∑a:Columns R δ,‖c a‖)*(A*(1+Real.log μ)^l*μ^(-(1/4:ℝ))):=by
  intro C δ site field
  have footprint(w):WilsonIndependentRawRosterBudget.span (x w) (site w) (ordered (I:=mask)) ≤ ap w:=by
    rw [entered.reach]
    exact reach w
  let submitted (a:Columns R δ)(w:Requests B.a):=Bare.normalized (W.tree (X w).F.p) G
    (film R W (fun _=>false) δ a (survey (X w) ray) (site w) ordered)
  let val(w:Requests B.a)(Z:PowerSeries ℂ):=
    PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (F (WilsonIndependentExactPlate.report V B.a w)) D Z)
  have prices (a:Columns R δ):∃u:ℝ,0 ≤ u ∧ ∃k:ℕ,∀w,
      ‖val w (submitted a w)-val w (field a w)‖ ≤ u*(1+Real.log ((V.step w.val).p.side.val:ℝ))^k*
        ((V.step w.val).p.side.val:ℝ)^(-(1/4:ℝ)):=
    WilsonIndependentReportedRoster.appointed R W P chart K V e h k j Y branches p b u extra col late B
      good paid ap positive F book orbit mask (fun _=>false) δ a ordered (fun w=>survey (X w) ray) site x c₀
      same footprint clear safe q hq D band hband sq
  choose cash hc power hp using prices
  have cp:0 ≤ ∑a,cash a:=Finset.sum_nonneg (fun i _=>hc i)
  refine ⟨∑a,cash a,cp,∑a,power a,?_⟩
  intro v w scale μ c
  have unit:1 ≤ μ:=by dsimp only [μ];exact_mod_cast (V.step w.val).p.side.pos
  have large:1 ≤ 1+Real.log μ:=by linarith [Real.log_nonneg unit]
  let bill:=(∑a,cash a)*(1+Real.log μ)^(∑a,power a)*μ^(-(1/4:ℝ))
  have each(a:Columns R δ):‖val w (submitted a w)-val w (field a w)‖ ≤ bill:=by
    apply (hp a w).trans (mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans unit) _))
    exact mul_le_mul (Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ a))
      (pow_le_pow_right₀ large (Finset.single_le_sum (fun i _=>Nat.zero_le (power i)) (Finset.mem_univ a)))
      (pow_nonneg (zero_le_one.trans large) _) cp
  have installed:=WilsonIndependentRawPhysicalFaces.received R W d (v w) (X w) ray mask ordered entered
  change WilsonOriginalPublicPivotReflected.board R W d (v w) (X w) mask=
    ∑a:Columns R δ,PowerSeries.C (c a)*submitted a w at installed
  rw [installed,linear,linear,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑a:Columns R δ,‖c a*val w (submitted a w)-c a*val w (field a w)‖:=norm_sum_le _ _
    _ ≤ ∑a:Columns R δ,‖c a‖*bill:=Finset.sum_le_sum fun a _=>by
      rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left (each a) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

end YM.Integration.WilsonIndependentReportedPhysicalTable
