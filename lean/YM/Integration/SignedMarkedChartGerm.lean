import YM.Comparison.RG02.Bulk.Admits
import YM.WilsonCoeffUV.Kinetic.Bridge
import YM.WilsonCoeffUV.Marked.Paths.Determinism

/-! The true marked field on the finite Wilson chart and the independently drawn heat source agree before integration. Every charged packet has its own valuation and its own joint source direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedMarkedChartGerm
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped Classical ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)

def chart (x : Sloc S F G) : Work.F03.ChartVars F G := (badge S F x,(sedan S F ρ x).1)

/-- One germ equality of the entire group-valued field, simultaneous before choosing any marked function, independent test or coefficient. -/
theorem configuration (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    (fun x : Sloc S F G=>input G f (camSlice G S F M *ᵥ spider (shore S F M ρ) x))=ᶠ[𝓝 0]
      fun x=>Work.F03.live F (chart S F ρ x) := by
  filter_upwards [tilted S F M ρ hM hρ h0] with x hx
  simpa only [mantle_input,Work.F03.live,chart] using hx

/-- Every joint nonlinear observable can be placed on the very same measured field. -/
theorem fields (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    ∀ᶠ x : Sloc S F G in 𝓝 0,∀ (g : ℝ) (A : ℝ→ Config G f→ℂ),
      Bulk.posed S F A (g,chart S F ρ x)=A g (input G f (camSlice G S F M *ᵥ spider (shore S F M ρ) x)) := by
  filter_upwards [configuration S F M ρ hM hρ h0] with x hx g A
  exact congrArg (A g) hx.symm

private theorem meter_rank {r : ℕ} (T : Atom G r) (a : Site f) : (X:Ink (Woods G f))^r*Blue.flash (sprig (meter T a) r)=jet (meter T a) := by
  apply moves
  intro i hi
  have hp := (rays_jet ((meter_hot T a).contDiffAt (x:=0)).analyticAt r).mp (meter_shell T a) i hi
  rw [jet_apply]
  have hz : rye (meter T a) i=0 := funext fun u=>by rw [rye,hp];simp
  rw [hz,map_zero]

private theorem retool_X : retool (shore S F M ρ) (loom (camSlice G S F M) (X:Ink (Woods G f)))=X := by simp [loom,retool,reroll_X]

/-- The unmasked path packet is the originally prescribed full Taylor tensor after the actual nonlinear coordinate change, at every perturbative order. -/
theorem atom {r : ℕ} (T : Atom G r) (a : Site f) (hM : M=reveal G S F*((reveal G S F).transpose*M))
    (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    (X:Ink (Active G F ⊕ Woods G c))^r*retool (shore S F M ρ) (loom (camSlice G S F M) (Blue.flash (sprig (meter T a) r)))=
      jet (fun x : Sloc S F G=>T.unmasked (Work.F03.live F (chart S F ρ x)) a) := by
  let L := camSlice G S F M
  let θ := shore S F M ρ
  have ht := shore_green S F M ρ hρ h0
  have hz := shore_zero S F M ρ h0
  have hf := (meter_hot T a).contDiffAt (x:=0)
  have hl : Green (fun u=>meter T a (L *ᵥ u)) := (show ContDiffAt ℝ ω (meter T a) (L*ᵥ0) by simpa using hf).comp 0 (board L)
  have hh := congrArg (fun v=>retool θ (loom L v)) (meter_rank T a)
  simp only [map_mul,map_pow,show retool θ (loom L X)=X from retool_X S F M ρ] at hh
  apply hh.trans
  rw [loom_jet L _ hf,pivot,traveling (spider θ) (spider_green ht) (spider_zero hz) _ hl]
  apply jet_congr
  filter_upwards [configuration S F M ρ hM hρ h0] with x hx
  exact congrArg (fun U=>T.unmasked U a) hx

/-- Read the original finite coefficient era before its mark tests, retaining its own Laurent shift and all of its field slots. -/
theorem volume {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Comet G E r) (L : E→L[ℝ] ℝ) (e : ℕ) (hM : M=reveal G S F*((reveal G S F).transpose*M))
    (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    (X:Ink (Active G F ⊕ Woods G c))^r*retool (shore S F M ρ) (loom (camSlice G S F M) (Blue.flash (ply L.toLinearMap ((volumeR P e).1 f))))=
      X^e*jet (fun x : Sloc S F G=>(dip P L).unmasked (Work.F03.live F (chart S F ρ x)) 0) := by
  have hread : Blue.flash (ply L.toLinearMap ((volumeR P e).1 f))=X^e*Blue.flash (sprig (meter (dip P L) (0:Site f)) r) := by
    rw [volume_probe]
    ext1 i
    rw [coeff_X_pow_mul']
    unfold Blue.flash
    simp only [coeff_mk]
    split <;> simp_all [totalR]
  rw [hread,map_mul,map_pow,map_mul,map_pow,retool_X,mul_left_comm,atom S F M ρ _ _ hM hρ h0]

/-- Arbitrary clearing of every actual stored power, including negative inputs. The right side is an ordinary physical jet, with no division or pole at zero. -/
theorem cleared {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Comet G E r) (L : E→L[ℝ] ℝ) (e b t : ℕ) (ht : b+e=r+t)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    (X:Ink (Active G F ⊕ Woods G c))^b*retool (shore S F M ρ) (loom (camSlice G S F M) (Blue.flash (ply L.toLinearMap ((volumeR P e).1 f))))=
      X^t*jet (fun x : Sloc S F G=>(dip P L).unmasked (Work.F03.live F (chart S F ρ x)) 0) := by
  apply mul_left_cancel₀ (a:=(X:Ink (Active G F⊕Woods G c))^r) (pow_ne_zero _ X_ne_zero)
  rw [mul_left_comm (X^r),volume S F M ρ P L e hM hρ h0,←mul_assoc,←pow_add,ht,pow_add,mul_assoc]

end YM.Integration.SignedMarkedChartGerm
