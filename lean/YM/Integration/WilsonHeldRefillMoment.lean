import YM.Integration.WilsonHeldExteriorLaw
import YM.Integration.ActualScalarTransport
import YM.Integration.OriginalMarkedRelativeMoment

/-! Redraw the local links with a retained action at the given lower field,
keep the true exterior distribution, and then integrate the lower field
under its original Wilson marginal. The comparison uses the first absolute
moment of the full signed insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldRefillMoment
open Function MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "fine" => Config G (R.family.side (j+1) per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per (j+1)
local notation "down" => R.family.path.rep N per j
local notation "held" => WilsonHeldExteriorLaw.weight R N per j
local notation "restore" => WilsonHeldExteriorLaw.link_row R N per j
local notation "E₀" => actualAverage R.family (N:=N) (p:=per) (m:=j)

def redraw (N per j : ℕ) (saved : Set (Edge (Site (R.family.side (j+1) per))))
    (P : Rep G (R.family.side (j+1) per)) (f : Config G (R.family.side (j+1) per) → ℂ)
    (V : Config G (R.family.side j per)) : ℂ :=
  actualAverage R.family (N:=N) (p:=per) (m:=j) (WilsonHeldExteriorLaw.link_row R N per j saved V P f) V

private theorem weighted_meas (live : j+1 ≤ N) (P : Rep G (R.family.side (j+1) per)) (p : Measurable P.eval) :
    Measurable (fun z : coarse × fine => held z.1 P z.2) := by
  have kernel := (R.family.path.levels.clock.op j per).density_meas
    (R.family.path.levels.blocks j per).branches (R.family.path.β N per (j+1)) (G:=G)
  have downlaw := (down).envelope (R.makes.wilson.represents N per j ((Nat.le_succ j).trans live)).good
  exact ((kernel.comp (measurable_snd.prodMk measurable_fst)).mul (p.comp measurable_snd)).div
    (downlaw.meas.comp measurable_fst)

theorem measurable (live : j+1≤N) (saved : Set (Edge (Site (R.family.side (j+1) per))))
    (P : Rep G (R.family.side (j+1) per)) (p : Measurable P.eval) (f : fine → ℂ) (hf : Measurable f) :
    Measurable (redraw R N per j saved P f) := by
  let cut := WilsonHeldExteriorLaw.cut G saved
  let X := coarse × fine
  let Y := WilsonHeldExteriorLaw.Fields G savedᶜ
  let augment (w : X × Y) : X := (w.1.1,cut.symm ((cut w.1.2).1,w.2))
  have aug : Measurable augment :=
    (measurable_fst.comp measurable_fst).prodMk (cut.symm.measurable.comp
      ((measurable_fst.comp (cut.measurable.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
  have pw := weighted_meas R live P p
  have ow := weighted_meas R live (up) ((up).envelope (R.makes.wilson.represents N per (j+1) live).good).meas
  have den := (pw.comp aug).stronglyMeasurable.integral_prod_right' (ν:=WilsonHeldExteriorLaw.sheet G savedᶜ)
  have num := ((pw.smul (hf.comp measurable_snd)).comp aug).stronglyMeasurable.integral_prod_right'
    (ν:=WilsonHeldExteriorLaw.sheet G savedᶜ)
  exact ((ow.smul (den.measurable.inv.smul num.measurable)).stronglyMeasurable.integral_prod_right' (ν:=prior G _)).measurable

/-- The conditional is at the genuine held field and every exterior comes
from its full original posterior. The single exponential uses the oscillation
between two fields on the same fibre. -/
theorem held_comparison (live : j+1 ≤ N) (saved : Set (Edge (Site (R.family.side (j+1) per))))
    (P : Rep G (R.family.side (j+1) per)) (p : Envelope P.eval) {floor : ℝ} (fp : 0 < floor)
    (low : ∀ U, floor ≤ P.eval U) (J : fine → ℝ) (law : ∀ U, (up).eval U = P.eval U * Real.exp (-J U))
    {a : ℝ} (osc : ∀ U W : fine, (∀ e ∈ saved, U e = W e) → |J U - J W| ≤ a)
    (f : fine → ℂ) (hf : Envelope f) (V : coarse) :
    ‖E₀ f V - redraw R N per j saved P f V‖ ≤
      (Real.exp a - 1) * E₀ (fun U => ‖f U‖) V := by
  obtain ⟨c,hc,floorQ⟩ := WilsonHeldExteriorLaw.upper_floor R N per j live
  have q := (WilsonHeldExteriorLaw.regularity R N per j live V (up)
    ((up).envelope (R.makes.wilson.represents N per (j+1) live).good) hc floorQ).1
  obtain ⟨kept,t,ht,lower⟩ := WilsonHeldExteriorLaw.regularity R N per j live V P p fp low
  have factor (U : fine) : held V (up) U = held V P U * Real.exp (-J U) := by
    unfold WilsonHeldExteriorLaw.weight
    rw [law U]; ring
  have charge (U W : fine) (same : ((SelectedCofactorChamberMarginal.cut G saved) U).1 =
      ((SelectedCofactorChamberMarginal.cut G saved) W).1) : |J U - J W| ≤ a :=
    osc U W (fun e he => congrFun same (⟨e,he⟩ : saved))
  have result := OriginalMarkedRelativeMoment.integral saved q kept factor ht lower charge f hf
  have normed : (∫ U, held V (up) U ∂prior G _) = 1 := actualConditionalDensity_total R.family R.makes live V
  change ‖OriginalMarkedExteriorHaar.average (prior G _) (held V (up)) f -
    OriginalMarkedExteriorHaar.average (prior G _) (held V (up)) (restore saved V P f)‖ ≤ _ at result
  simp only [OriginalMarkedExteriorHaar.average,integral_complex_ofReal,normed,Complex.ofReal_one,inv_one,one_mul] at result
  have same (U : fine) : held V (up) U = actualConditionalDensity R.family N per j V U := rfl
  simpa only [redraw,actualAverage,Complex.real_smul,smul_eq_mul,same] using result

private theorem measured_norm (live : j+1 ≤ N) (f : fine → ℂ) (hf : Envelope f) :
    Integrable (E₀ (fun U => ‖f U‖)) (scene R.family.path N per j) ∧
    (∫ V, E₀ (fun U => ‖f U‖) V ∂scene R.family.path N per j) =
      ∫ U, ‖f U‖ ∂scene R.family.path N per (j+1) := by
  have ef : Envelope (fun U => ‖f U‖) := by
    obtain ⟨C,hC⟩ := hf.cost
    exact ⟨hf.meas.norm,C,fun U => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hC U⟩
  have top := (((up).envelope (R.makes.wilson.represents N per (j+1) live).good).mul ef).integrable (prior G _)
  have same : actualTransport R.family (N:=N) (fun U => ‖f U‖) (Nat.le_succ j) = E₀ (fun U => ‖f U‖) := by
    rw [actualTransport_step R.family R.makes live _ (Nat.lt_succ_self j),actualTransport_base R.family R.makes live]
  rw [←same]
  refine ⟨actualScene_integrable_of_weighted R.family R.makes ((Nat.le_succ j).trans live)
    (actualTransport_weighted_integrable_of_integrable R.family R.makes live top (Nat.le_succ j)),?_⟩
  exact actualScene_transport R.family R.makes live top (Nat.le_succ j)

/-- Pay an arbitrary signed local exception on the retained action by the
original upper expectation, after integrating the TRUE held exterior. -/
theorem original (live : j+1 ≤ N) (saved : Set (Edge (Site (R.family.side (j+1) per))))
    (P : Rep G (R.family.side (j+1) per)) (p : Envelope P.eval) {floor : ℝ} (fp : 0 < floor)
    (low : ∀ U, floor ≤ P.eval U) (J : fine → ℝ) (law : ∀ U, (up).eval U = P.eval U * Real.exp (-J U))
    {a : ℝ} (osc : ∀ U W : fine, (∀ e ∈ saved, U e = W e) → |J U - J W| ≤ a)
    (f : fine → ℂ) (hf : Envelope f) :
    Integrable (redraw R N per j saved P f) (scene R.family.path N per j) ∧
    (∫ V, ‖redraw R N per j saved P f V‖ ∂scene R.family.path N per j) ≤
      Real.exp a * ∫ U, ‖f U‖ ∂scene R.family.path N per (j+1) := by
  obtain ⟨hi,eq⟩ := measured_norm R live f hf
  have bound (V : coarse) : ‖redraw R N per j saved P f V‖ ≤ Real.exp a * E₀ (fun U => ‖f U‖) V := by
    have old : ‖E₀ f V‖ ≤ E₀ (fun U => ‖f U‖) V := by
      unfold actualAverage
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul,Real.norm_of_nonneg (actualConditionalDensity_nonneg R.family R.makes live V _),smul_eq_mul]
    have change := held_comparison R live saved P p fp low J law osc f hf V
    rw [norm_sub_rev] at change
    calc
      _ = ‖(redraw R N per j saved P f V - E₀ f V) + E₀ f V‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le ..).trans (by linarith only [old,change])
  have intg := hi.const_mul (Real.exp a)
  refine ⟨intg.mono' (measurable R live saved P p.meas f hf.meas).aestronglyMeasurable
    (ae_of_all _ bound),?_⟩
  exact (integral_mono_of_nonneg (ae_of_all _ (fun V => norm_nonneg _)) intg (ae_of_all _ bound)).trans_eq
    (by rw [integral_const_mul,eq])

end YM.Integration.WilsonHeldRefillMoment
