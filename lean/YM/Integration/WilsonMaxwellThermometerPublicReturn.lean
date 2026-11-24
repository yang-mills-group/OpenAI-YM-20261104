import YM.Integration.WilsonMaxwellThermometerPublicPocket
import YM.Integration.WilsonPositionThermometerSevenFaceRate

/-! Restoring the signed grade-four projection of the genuine public field
costs little-o of the reporter's own coupling. Either one coupling price
on the lower triangles, or one on the true public calibration survey,
suffices together with convergence of the other factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicReturn
open Filter Lattice Wilson RG Maxwell Maxwell.Free RG17 XSpace XSpace.Normalize
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicPocket
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→PhysMS.tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)
  (Y:Ultrafilter (ℕ×ℕ)) (simple:G.Simple) (B:ℕ)
  {I:Type} [Fintype I] (D:RG17.Free R.family 6 →L[ℂ] (I→ℂ)) (e:I→RG17.Free R.family 4)
local notation "L" => trail.curry (Y:Filter (ℕ×ℕ))
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)
local notation "v" => coordinates R F J V D
local notation "s" => WilsonMaxwellThermometerPublicPocket.measured R F J V K A

def bill (r:ℝ) (z:ℕ×ℕ):ℂ:=
  receipt R (WilsonPositionCorrectedCap.adjusted F J V A r) r z (Rose.test K)
    (∑i,v r i • shoulder R (A r) z (e i))

private theorem sum_price (r:ℝ) (z:ℕ×ℕ) :
    ‖bill R F J V K A D e r z‖≤∑i,‖v r i‖*‖s r z (e i)‖:=by
  rw [bill,WilsonMaxwellThermometerPublicPocket.reading]
  simpa only [norm_mul] using norm_sum_le Finset.univ (fun i=>v r i*s r z (e i))

theorem triangles (lead:Leading F J) (C:ℝ) (positive:0<C)
    (charged:∀ᶠw:ℝ×(ℕ×ℕ) in L,∀i,‖s w.1 w.2 (e i)‖≤C*|g w.1 w.2|):
    ∀ε>0,∀ᶠw:ℝ×(ℕ×ℕ) in L,‖bill R F J V K A D e w.1 w.2‖≤ε*|g w.1 w.2|:=by
  have radius:Tendsto (Prod.fst:ℝ×(ℕ×ℕ)→ℝ) L trail:=tendsto_fst.mono_left Filter.curry_le_prod
  have each (i:I):Tendsto (fun w:ℝ×(ℕ×ℕ)=>‖v w.1 i‖) L (𝓝 0):=by
    have h:=((continuous_apply i).tendsto (0:I→ℂ)).comp ((small R F J V lead D).comp radius)
    simpa only [Function.comp_def,Pi.zero_apply,norm_zero] using h.norm
  have many:Tendsto (fun w:ℝ×(ℕ×ℕ)=>∑i,‖v w.1 i‖) L (𝓝 0):=by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>each i)
  intro ε he
  filter_upwards [many.eventually (gt_mem_nhds (div_pos he positive)),charged] with w tiny priced
  calc
    _ ≤ ∑i,‖v w.1 i‖*‖s w.1 w.2 (e i)‖:=sum_price R F J V K A D e _ _
    _ ≤ ∑i,‖v w.1 i‖*(C*|g w.1 w.2|):=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (priced i) (norm_nonneg _)
    _ = (∑i,‖v w.1 i‖)*C*|g w.1 w.2|:=by rw [←Finset.sum_mul,mul_assoc]
    _ ≤ ε*|g w.1 w.2|:=mul_le_mul_of_nonneg_right ((le_div_iff₀ positive).mp tiny.le) (abs_nonneg _)

theorem survey (lead:Leading F J) (C:ℝ) (positive:0<C)
    (paid:∀ᶠw:ℝ×(ℕ×ℕ) in L,WilsonPositionOriginalCalibrationSensitivity.price F J V 6 w.1 ≤ C*|g w.1 w.2|)
    (vanish:∀i,Tendsto (fun w:ℝ×(ℕ×ℕ)=>s w.1 w.2 (e i)) L (𝓝 0)):
    ∀ε>0,∀ᶠw:ℝ×(ℕ×ℕ) in L,‖bill R F J V K A D e w.1 w.2‖≤ε*|g w.1 w.2|:=by
  obtain ⟨c,hc,fee⟩:=signed R F J V lead D
  let M:=max 1 c * C
  have hm:0<M:=mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) positive
  have radius:Tendsto (Prod.fst:ℝ×(ℕ×ℕ)→ℝ) L trail:=tendsto_fst.mono_left Filter.curry_le_prod
  have many:Tendsto (fun w:ℝ×(ℕ×ℕ)=>∑i,‖s w.1 w.2 (e i)‖) L (𝓝 0):=by
    simpa only [norm_zero,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>(vanish i).norm)
  intro ε he
  filter_upwards [many.eventually (gt_mem_nhds (div_pos he hm)),paid,radius.eventually fee] with w tiny rate priced
  have price(i:I):‖v w.1 i‖≤M*|g w.1 w.2|:=calc
    _ ≤ ‖v w.1‖ := norm_le_pi_norm _ _
    _ ≤ c*WilsonPositionOriginalCalibrationSensitivity.price F J V 6 w.1 := priced
    _ ≤ c*(C*|g w.1 w.2|):=mul_le_mul_of_nonneg_left rate hc
    _ ≤ M*|g w.1 w.2|:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) positive.le) (abs_nonneg _)
  calc
    _ ≤ ∑i,‖v w.1 i‖*‖s w.1 w.2 (e i)‖:=sum_price R F J V K A D e _ _
    _ ≤ ∑i,(M*|g w.1 w.2|)*‖s w.1 w.2 (e i)‖:=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (price i) (norm_nonneg _)
    _ = (∑i,‖s w.1 w.2 (e i)‖)*M*|g w.1 w.2|:=by rw [←Finset.mul_sum]; ring
    _ ≤ ε*|g w.1 w.2|:=mul_le_mul_of_nonneg_right ((le_div_iff₀ hm).mp tiny.le) (abs_nonneg _)

end YM.Integration.WilsonMaxwellThermometerPublicReturn
