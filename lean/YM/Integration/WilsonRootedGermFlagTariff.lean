import YM.Integration.WilsonMatrixOriginalGermHeldTest
import YM.Integration.ActualRunRequestedNorm
import YM.Integration.SelectedCofactorVacuumMass
import YM.TraceExtension.Terrace.Lyre
import YM.TraceExtension.Terrace.Virtu
import YM.OPE.Therm.Request
import YM.Vac.Treasury

/-! Per occupied flag on the original representation, with a real number of sites per flag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermFlagTariff
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Source Labels Cells
open Extra.Histories Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open OPE.Therm Trace.Terrace IterationFour
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def siteRate (R : Run G) (i N per : ℕ) : ℝ :=
  let L := R.family.path.levels
  let W := R.family.path.rep N per i
  let A := (L.params i).paths
  let s := L.clock.hatCoupling i
  2*W.exCost A (L.clock.loopCap i) (L.clock.allowance i) + W.beta*RG.baseBudget W.clip A s +
    4*Module.finrank ℝ G.Mat*Real.log (16/s)

def heat (R : Run G) (i N per : ℕ) : ℝ :=
  let W := R.family.path.rep N per i
  W.beta*(W.clip.linear/5*((R.family.path.levels.budget i).threshold/2)^2)

theorem stock (R : Run G) (N per i : ℕ) (hi : i≤N) :
    let L := R.family.path.levels
    let W := R.family.path.rep N per i
    let A := (L.params i).paths
    let s := L.clock.hatCoupling i
    2*W.exCost A (L.clock.loopCap i) (L.clock.allowance i)+W.beta*RG.baseBudget W.clip A s+
      4*Module.finrank ℝ G.Mat*Real.log (16/s) ≤ Vac.treasury L i := by
  intro L W A s
  have h := Vac.suffices_bill R.makes.wilson (p := per) hi 0 0 0 0 0
  unfold Overlay.Bands.finalBill at h
  simp only [Nat.cast_zero,zero_mul,add_zero] at h
  let sites := (Fintype.card (Site (R.family.side i per)):ℝ)
  have hp : 0<sites := by dsimp only [sites];exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Site (R.family.side i per)))
  have hw : 0≤L.clock.forcedAllowance i := (Real.exp_pos _).le
  have hv : sites*(2*W.exCost A (L.clock.loopCap i) (L.clock.allowance i)+L.clock.forcedAllowance i+
      W.beta*RG.baseBudget W.clip A s+4*Module.finrank ℝ G.Mat*Real.log (16/s))≤ sites*Vac.treasury L i := h
  have hh := le_of_mul_le_mul_left hv hp
  linarith only [hh,hw]

theorem purchased (R : Run G) (hG : G.Simple) (theta : Poetry R.family.path.levels) (e target : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ N per, i≤N → ∀ width : ℝ, 0≤width → width≤Lyra R.family.path.levels i^e →
      width*siteRate R i N per - heat R i N per ≤ -(target:ℝ)*Lyra R.family.path.levels i := by
  let L := R.family.path.levels
  let m := e+2
  filter_upwards [(lrate L hG).eventually_ge_atTop (max 40 (target:ℝ)),
    (hrate L hG).eventually (Lyra_small (m+2) (c := 1) zero_lt_one),Vac.treasury_stage L hG]
    with i hlarge hmonitor hfiat
  intro N per hi width hwidth hside
  let W := R.family.path.rep N per i
  let b := Lyra L i
  let a := L.clock.hatBeta i
  let u := L.clock.monitor i
  let c := (L.params i).clip.linear
  let t := (L.budget i).threshold
  have h40 : 40≤b := (le_max_left _ _).trans hlarge
  have hb : 1≤b := by linarith only [h40]
  have hb0 := zero_le_one.trans hb
  have ht : (target:ℝ)≤b := (le_max_right _ _).trans hlarge
  have htreasury : Vac.treasury L i≤b^2 :=
    (theta.stage i).price.trans' (hfiat.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have he : width*Vac.treasury L i≤b^m := by
    calc
      _ ≤ width*b^2 := mul_le_mul_of_nonneg_left htreasury hwidth
      _ ≤ b^e*b^2 := mul_le_mul_of_nonneg_right hside (sq_nonneg b)
      _ = _ := by dsimp only [m];rw [pow_add]
  have hv : 1≤u := Real.one_le_exp (sq_nonneg _)
  have hvp : b^(m+2)≤u := by change _≤L.clock.monitor i;rw [oracle];exact hmonitor
  have hv2 : u≤u^2 := by nlinarith only [mul_nonneg (zero_le_one.trans hv) (sub_nonneg.mpr hv)]
  have hh : 40*(b^m*b)≤u^2 := by
    calc
      _ ≤ b*(b^m*b) := mul_le_mul_of_nonneg_right h40 (by positivity)
      _ = b^(m+2) := by rw [pow_add];ring
      _ ≤ _ := hvp.trans hv2
  have cpos : 0<c := (L.params i).clip.tail_pos
  have hstrain : 10≤b*c := (div_le_iff₀ cpos).mp (theta.stage i).strain
  have hc : 2*b^m≤u^2*c/40 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<40)).mpr
    calc
      _ ≤ 40*b^m*10 := by nlinarith only [pow_nonneg hb0 m]
      _ ≤ 40*b^m*(b*c) := mul_le_mul_of_nonneg_left hstrain (by positivity)
      _ = (40*(b^m*b))*c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh cpos.le
  have ha : 0<a := zero_lt_one.trans (L.fits.delayed i)
  have hat : a*t^2=u^2 := by
    change a*((Real.sqrt a)⁻¹*u)^2=u^2
    rw [mul_pow,inv_pow,Real.sq_sqrt ha.le,←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
  have hw := R.makes.wilson.represents N per i hi
  have hflag : 2*b^m≤W.beta*(c/5*(t/2)^2) := by
    calc
      _ ≤ u^2*c/40 := hc
      _ = (a/2)*(c/5*(t/2)^2) := by rw [←hat];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw.band.1 (by positivity)
  have htarget : (target:ℝ)*b≤b^m := by
    calc
      _ ≤ b*b := mul_le_mul_of_nonneg_right ht hb0
      _ = b^2 := by ring
      _ ≤ b^m := pow_le_pow_right₀ hb (by dsimp only [m];omega)
  have hl := (mul_le_mul_of_nonneg_left (stock R N per i hi) hwidth).trans he
  unfold siteRate heat
  change width*(_+_+_)-W.beta*(W.clip.linear/5*(t/2)^2)≤-(target:ℝ)*b
  rw [show W.clip=(L.params i).clip from hw.clip]
  change width*(_+_+_)-W.beta*(c/5*(t/2)^2)≤-(target:ℝ)*b
  rw [show W.clip=(L.params i).clip from hw.clip] at hl
  linarith only [hl,hflag,htarget]

end YM.Integration.WilsonRootedGermFlagTariff
