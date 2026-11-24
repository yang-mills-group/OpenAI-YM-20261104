import YM.Integration.FVA1Physical.Wilson.HotelBank
import YM.Integration.FVA1Physical.Sources.Round2.TwoThermalSeasons

/-! At every period a single physically sampled forest collar suffices for the
full independent outgoing mixed-field Wilson stencil under the next Haar
posterior. All errors are on the original measured vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open Push.Uniform MSbar.Midpoint MSbar.Bakery.Film MSbar.Bakery MSbar.Measuring
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open Progress.DirectedRecipe PhysicalNext.Repeat.Legato Next.Foundations Next.SectorChange Extra.Iteration
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι]

theorem uncut_hotel_stencil (J:ι→Lamp G) (V:Voice G) (cle:Clear G V) (χ:ChartRatio G) (simple:G.Simple)
    (H H' H'':RG.Stage) (P₀ P₁:Patch) (K₀:KernelChoices) (br:P₀.Branches K₀ G) (m s p:ℕ)
    {D:ℝ} (hD:0 ≤ D) (exp:ℝ) :
    ∀ᶠ x:ℝ in atTop,∀ {C:Family G} (chain:Comparison.RG02.Bulk.Chain C.path)
      {N n j r:ℕ} (T:Scene C.path.levels n r) (F:Forest (C.path.levels.clock.op j n).ratio)
      (v:(C.path.levels.clock.op j n).Choices) (F':Forest (C.path.levels.clock.op (j+1) n).ratio)
      (v':(C.path.levels.clock.op (j+1) n).Choices),
      let B:=sceneIssue (N:=N) chain T F v
      let A:=sceneIssue (N:=N) chain T F' v'
      let y:=tip G P₀.L x
      B.S.patch=P₀ → B.S.kernel=K₀ → Season V H H' x B.pre B.post B.S (courage G P₀.L x) →
      A.S.patch=P₁ → Season V H' H'' y A.pre A.post A.S (courage G P₁.L y) →
      ∀ (b:Site B.f) (Z:Positions (Primary B.c G)) (o:ι→Site A.f) (part:Bool), ‖Z‖ ≤ D*room y →
      BankPaid b y s p m 1 (emittedRows A χ (jointFieldBank J A o part) p) →
      let O:=represent (tint G (Body 1 B.c) Z)
      let μ:=vest (priced B.F B.v B.pre.clip B.pre.path) Z
      let live:=hotel B.F (boxX y b) (boxY y b) V O μ (pillow y) (room y)
      let copy:=chambers B.F (boxY y b) V O μ
      let P:=independentStencil J A χ p o part
      let E:=expect B.S B.pre O
      |E (live.indicator (P ∘ copy))-E (P ∘ canoe (S:=B.S) B.F)| ≤ (p+2:ℕ)*y^exp := by
  let d:ℝ:=(m+3:ℕ)
  obtain ⟨_,pay⟩:=purchased_fluctuation_chance V cle simple H H' P₀ K₀ br hD (exp-d)
  have grow:=Work.E09.betaF_growth G P₀.L
  have fine:=Work.E09.betaF_growth G P₁.L
  have padded:∀ᶠ y:ℝ in atTop,pillow y ≤ room y := by
    filter_upwards [(Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 3,
      eventually_ge_atTop (1:ℝ)] with y lo hi
    have nn:0 ≤ distance y:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _) (Real.log_nonneg hi)
    simpa only [pillow,Cottage.room,Function.comp_apply,mul_comm (3:ℝ) _] using mul_le_mul_of_nonneg_left lo nn
  filter_upwards [pay,grow.eventually (hotel_bank_mean (ι:=ι) G m s p (-exp)),grow.eventually padded,
    grow.eventually_gt_atTop 0,grow.eventually_ge_atTop (|G.slopeConstant*Real.log P₁.L.val|),
    (fine.comp grow).eventually_ge_atTop 8] with x buy transfer pad y0 diff z8
  intro C chain N n j r T F v F' v' B A y p₀ k₀ out p₁ inn b Z o part hZ bank O μ live copy P E
  let z:=tip G P₁.L y
  have high : 8 ≤ z:=z8
  have z1:1 ≤ z:=by linarith
  have clock:=inn.case_
  rw [p₁] at clock
  have band:lensT z A.fClock:=Mosaic.ever (zero_lt_one.trans_le z1) clock.beta clock.upper
  have ⟨g0,invG⟩:=inverse_clock_le_linear z1 band
  have zy : z ≤ 2*y := by
    change y+G.slopeConstant*Real.log P₁.L.val ≤ 2*y
    change |G.slopeConstant*Real.log P₁.L.val| ≤ y at diff
    linarith only [(le_abs_self _).trans diff]
  have small:|A.fClock| ≤ 1 := by
    rw [abs_of_pos g0]
    have two: (2:ℝ) ≤ Real.sqrt z := (show (2:ℝ)=Real.sqrt 4 by norm_num).le.trans
      (Real.sqrt_le_sqrt (by linarith : 4 ≤ z))
    exact band.2.trans (by change 2*(Real.sqrt z)⁻¹ ≤ 1;rw [←div_eq_mul_inv];exact (div_le_one (lt_of_lt_of_le (by norm_num) two)).mpr two)
  have adm:Admitted O B.pre B.S H'.width H'.paths (ability (tip G B.S.patch.L x)) (lbt (tip G B.S.patch.L x)) 1 :=
    ⟨out.case_.lawful,fun U=>(out.shine U).le,push_strict B.S B.pre.beta out.bends.1 out.shine
      ((B.pre.envelope out.case_.lawful).integrable _) O,B.S.isKernel out.bends.1 _⟩
  obtain ⟨_,cal,_,_⟩:=buy B p₀ k₀ out Z b hZ
  have result:=transfer A J χ part o b (invG.trans (by linarith only [zy])) small bank
    B.S B.pre O adm B.F V μ cle pad (y^(exp-d)) cal.sails
  have pow:y^(m+3)*y^(exp-d)=y^exp := by
    rw [←Real.rpow_natCast,←Real.rpow_add y0]
    congr 1;dsimp only [d];ring
  exact result.trans_eq (by rw [neg_neg,pow];push_cast;ring)

end YM.Integration.FVA1Physical.Wilson
