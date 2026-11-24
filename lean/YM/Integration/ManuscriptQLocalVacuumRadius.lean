import YM.Integration.ZeroAwareCappedCreditPolynomial
import YM.Integration.FullQLocalNumericStepData
import YM.Integration.FullQLocalCostSubpower

/-!
# The genuine old vacuum rows at the engineering radius

The regulator prefactor and the auxiliary Taylor degree are different on a curved
row.  The latter acts on its nominal power.  Each original row keeps its genuine
support, all physical Lie derivatives, and the compulsory gas on the incoming carrier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalVacuumRadius
open Filter Lattice Wilson RG IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped BigOperators Classical Topology

variable {G : Gauge} {n : Side} {S : List (Piece G n)} {p : BudgetPoint}
  {cap : ℕ} {width budget : ℝ}

def weight (g z : ℝ) (a : Piece G n) : ℝ := z^a.power*Render.prefactor g a

def bill (H : ZeroAwareVacuumPackets S p cap width budget) (g z : ℝ) : ℝ :=
  (S.map fun a=>‖weight g z a‖*ZeroAwareCappedRenderInvoice.credit H a).sum

/-- The original activities with their full differentiated regular hull, every
inherited forced row and the calibrated signed angular field. -/
theorem carrier (H : ZeroAwareVacuumPackets S p cap width budget)
    (hp : Render.permits S p) (hw : 0<width) (g z : ℝ)
    (E : Activities G n) {t k : ℝ} (hE : E.Valid p t k) :
    (Render.adorn (weight g z) E S).Valid p (t+bill H g z) k := by
  have load (l : List (Piece G n)) (hl : l⊆S) :
      (Render.adorn (weight g z) E l).Valid p
        (t+(l.map fun a=>‖weight g z a‖*ZeroAwareCappedRenderInvoice.credit H a).sum) k := by
    induction l with
    | nil => simpa only [Render.adorn,List.map_nil,List.sum_nil,add_zero] using hE
    | cons a l ih =>
      have tail:=ih (fun b hb=>hl (List.mem_cons_of_mem a hb))
      have added:=Payload.payment (weight g z a)
        (ZeroAwareCappedRenderInvoice.invoice H hp hw a (hl List.mem_cons_self)) tail
      simpa only [Render.adorn,List.map_cons,List.sum_cons,add_assoc,add_left_comm,add_comm] using added
  exact load S (fun _ h=>h)

theorem forced (g z : ℝ) (E : Activities G n) (l : List (Piece G n)) :
    (Render.adorn (weight g z) E l).forced = E.forced ∧
    (Render.adorn (weight g z) E l).K = E.K := by
  induction l with
  | nil => exact ⟨rfl,rfl⟩
  | cons a l ih => exact ih

private theorem together (a : Piece G n) {g : ℝ} (hg : 0<g) (z : ℝ) :
    ‖weight g z a‖*p.threshold^a.rank =
      (|z| *g)^a.power*(p.threshold/g)^a.rank := by
  have h : ‖Render.prefactor g a‖*p.threshold^a.rank =
      g^a.power*(p.threshold/g)^a.rank := by
    rw [Render.prefactor,Render.stepOrder,Real.norm_of_nonneg (zpow_nonneg hg.le _),
      zpow_natCast_sub_natCast₀ hg.ne',div_pow]
    ring
  rw [weight,norm_mul,norm_pow,Real.norm_eq_abs,mul_assoc,h,mul_pow]
  ring

/-- The full source radius is a genuine input to the same original per-root
regular invoice. No small-mark normalization enters the bound. -/
theorem priced (G : Gauge) (cap o d : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ D : ℕ,∀ {n : Side} {L : List (Piece G n)} {p : BudgetPoint}
      {width budget : ℝ} (H : ZeroAwareVacuumPackets L p cap width budget),
      p.order=o → p.power=d → 0<width → ∀ {q : ℕ},(∀a∈L,q≤a.power) →
      ∀ {g z W : ℝ},0<g → |z| *g≤1 → 1≤W → p.threshold/g≤W →
      bill H g z ≤ (|z| *g)^q*(C*(1+width⁻¹)^D*budget^2*W^cap) := by
  obtain ⟨C,hC,D,credit⟩:=ZeroAwareCappedCreditPolynomial.credit_bound G cap o d
  refine ⟨C,hC,D,?_⟩
  intro n L p width budget H ho hd hw q hq g z W hg hz hW hr
  have hB : 0≤budget := (Real.exp_pos _).le.trans H.cover_cost
  have hZ : 0≤|z| *g := mul_nonneg (abs_nonneg _) hg.le
  let price:=(|z| *g)^q*W^cap*(C*(1+width⁻¹)^D*budget)
  have hpr : 0≤price := by dsimp only [price]; positivity
  have one (a : Piece G n) (ha : a∈L) :
      ‖weight g z a‖*ZeroAwareCappedRenderInvoice.credit H a ≤ price*H.pieceCost a := by
    have small:=pow_le_pow_of_le_one hZ hz (hq a ha)
    have rank:=(pow_le_pow_left₀ (div_nonneg p.threshold_pos.le hg.le) hr a.rank).trans
      (pow_le_pow_right₀ hW (H.rank_bounded a ha))
    have all:=mul_le_mul small rank (pow_nonneg (div_nonneg p.threshold_pos.le hg.le) _)
      (pow_nonneg hZ _)
    have paid:=mul_le_mul_of_nonneg_left (credit H ho hd hw a ha) (norm_nonneg (weight g z a))
    have hc:0≤C*(1+width⁻¹)^D*budget*H.pieceCost a := by
      have := H.piece_cost_nonnegative a ha
      positivity
    calc
      _ ≤ ‖weight g z a‖*(C*p.threshold^a.rank*(1+width⁻¹)^D*budget*H.pieceCost a) := paid
      _ = ((|z| *g)^a.power*(p.threshold/g)^a.rank)*(C*(1+width⁻¹)^D*budget*H.pieceCost a) := by
        rw [←together a hg z]; ring
      _ ≤ ((|z| *g)^q*W^cap)*(C*(1+width⁻¹)^D*budget*H.pieceCost a) :=
        mul_le_mul_of_nonneg_right all hc
      _ = _ := by dsimp only [price]; ring
  have summ (l : List (Piece G n)) (hl : l⊆L) :
      (l.map fun a=>‖weight g z a‖*ZeroAwareCappedRenderInvoice.credit H a).sum ≤
        price*(l.map H.pieceCost).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,mul_add]
      exact add_le_add (one a (hl List.mem_cons_self)) (ih (fun b hb=>hl (List.mem_cons_of_mem a hb)))
  exact (summ L (fun _ h=>h)).trans ((mul_le_mul_of_nonneg_left H.total hpr).trans_eq
    (by dsimp only [price]; ring))

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
  (R : Run G) {J : Request V} (A : NumericSchedule R.family J)

theorem original (hG : G.Simple) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m in (atTop : Filter ℕ),∀ (d : LocalFormal.Datum R.family Γ),d.level=m →
      ∀ (F : AnalyticInput J A d) (z : ℝ),
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      |z| *g≤1 → bill F.vacuum.packets g z ≤ (|z| *g)^3*g^(-ε) := by
  obtain ⟨C,hC,D,paid⟩:=priced G J.vacuumRankCap J.inputFieldOrder J.inputDistanceOrder
  let e:=D+2+J.vacuumRankCap
  have sub:=PreRun.CostProfile.scalar_subpower_mul R (fun _=>C) (fun m=>A.admittedCost m^e)
    (fun m=>pow_nonneg (A.admitted_cost_nonnegative m) _)
    (PreRun.CostProfile.scalar_subpower_constant R hG A C)
    (PreRun.CostProfile.scalar_subpower_pow R hG A A.admittedCost A.admitted_cost_nonnegative
      (PreRun.CostProfile.scalar_subpower_of_schedule R A) e)
  filter_upwards [sub ε hε] with m cost d hd F z g hz
  subst m
  let B:=A.admittedCost d.level
  have hg : 0<g:=Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have hB : 1≤B:=A.admitted_cost_ge_one _
  have hww := A.cost_covers_widths d.level
  have hwide : 1+(A.inputWidth d.level)⁻¹≤B := by
    have h0:=inv_nonneg.mpr (A.output_width_pos d.level).le
    linarith only [hww,h0,A.radius_loss_ge_one d.level]
  have ratio : (A.inputNorm d.level).threshold/g≤B := by
    rw [(A.input_norm d.level).threshold]
    have h0:0≤R.family.path.levels.clock.threshold d.level/g :=
      div_nonneg (R.family.path.levels.budget d.level).threshold_pos.le hg.le
    change R.family.path.levels.clock.threshold (d.level+1)/g≤A.admittedCost d.level
    linarith only [A.cost_covers_units d.level d.cutoff d.period d.below,h0]
  have lower (a) (ha:a∈F.layers) : 3≤a.power := (F.vacuum.orders a ha).1
  have hh:=paid F.vacuum.packets (A.input_norm d.level).order (A.input_norm d.level).distance
    (A.input_width_pos d.level) lower hg hz hB ratio
  have hwD:=pow_le_pow_left₀ (add_nonneg zero_le_one (inv_nonneg.mpr (A.input_width_pos d.level).le)) hwide D
  have price : C*(1+(A.inputWidth d.level)⁻¹)^D*B^2*B^J.vacuumRankCap ≤ C*B^e := by
    calc
      _ ≤ C*B^D*B^2*B^J.vacuumRankCap := by gcongr
      _ = _ := by dsimp only [e]; rw [pow_add,pow_add]; ring
  exact hh.trans (mul_le_mul_of_nonneg_left (price.trans (cost d.cutoff d.period d.below))
    (pow_nonneg (mul_nonneg (abs_nonneg _) hg.le) _))

/-- One cofinal margin for every auxiliary point up to the true graded radius.
At the measured coupling the old signed source is recovered by z=1. -/
theorem collar (hG : G.Simple) {η : ℝ} (hη : 0<η) :
    ∀ᶠ m in (atTop : Filter ℕ),∀ (d : LocalFormal.Datum R.family Γ),d.level=m →
      ∀ (F : AnalyticInput J A d) (z : ℝ),
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      |z| *g≤g^η → bill F.vacuum.packets g z ≤ g^(2*η) := by
  filter_upwards [original R A hG hη,
    (tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)]
    with m quote small d hm F z g hz
  subst m
  have hg:0<g:=Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have hg1:g≤1:=(small d.cutoff d.period d.below).le
  have hc:|z| *g≤1:=hz.trans (Real.rpow_le_one hg.le hg1 hη.le)
  calc
    _ ≤ (|z| *g)^3*g^(-η) := quote d rfl F z hc
    _ ≤ (g^η)^3*g^(-η) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hg.le) hz 3) (Real.rpow_nonneg hg.le _)
    _ = g^(2*η) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hg.le,←Real.rpow_add hg]
      congr 1
      push_cast
      ring

end YM.Integration.ManuscriptQLocalVacuumRadius
