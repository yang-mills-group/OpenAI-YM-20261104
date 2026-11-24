import YM.RG02.Flat.Forest
import YM.RG02.Flat.Kernel

/-!
# On a local generating set of physical Haar fields

Provide the exact analytic collar criterion. V background t • x; affine
chart multiplier is part of the same Haar operation, not a centered density
chosen a posteriori. No Jacobian simplification off the declared domain.
Use Layer even with parameter-varying sets in local RG analytic consumer;
no-tail estimates across the boundary are not a consequence of these pointwise
facts. Reusable for moving the stationary centering. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Volume
open Filter Function MeasureTheory Set Metric Lattice Exterior Tree Wilson RG Precision
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius ENNReal Pointwise
variable {G : Gauge} {c f : Side}{g : Lattice.Ratio c f}(T : Forest g)

lemma paid (a : T.Slice G) : MeasurePreserving (fun x=>x*a) (T.order G) (T.order G) := by
   unfold Forest.order; exact measurePreserving_pi _ _ (fun i : T.Free=> measurePreserving_mul_right G.probHaar (a i))

def coordinate (a : T.Slice G) (s : AxisChart G T) := Chart.expLinks G T.Free s * a

lemma coordinate_cont : Continuous (uncurry (coordinate T (G:=G))) :=
   (continuous_pi (fun i:T.Free => G.lieExp_cont.comp ((continuous_apply i).comp continuous_snd))).mul continuous_fst

def block (r : ℝ)(a : T.Slice G) : Set (T.Slice G) := (fun x : T.Slice G => x * a⁻¹) ⁻¹' Chart.chamber G T.Free r

lemma block_open {η : ChartRatio G} (h : LocalRatio η)(a : T.Slice G){r : ℝ}(hr:r≤ Chart.small G η) : IsOpen (block T r a) :=
    (Chart.Ratio.chamber_open h hr).preimage (continuous_mul_const _)

def base (e : ℝ)(a : T.Slice G)(U : Set (T.Slice G)) := coordinate T a ⁻¹' U ∩ Metric.ball 0 e

def inside (e : ℝ) (a : T.Slice G)(U : Set (T.Slice G))(t : ℝ) := (fun v : AxisChart G T=>t • v) ⁻¹' base T e a U

lemma inside_meas (e t : ℝ) (a : T.Slice G){U : Set (T.Slice G)}(h : MeasurableSet U) : MeasurableSet (inside T e a U t) := by
   let H := show Continuous (coordinate T a) from (coordinate_cont T).comp (f:=fun (x:AxisChart G T) => (a,x)) (continuous_const.prodMk continuous_id)
   exact (show Continuous fun v:AxisChart G T=>t • v from by fun_prop).measurable ((H.measurable h).inter isOpen_ball.measurableSet)

lemma selected {η : ChartRatio G} (h : LocalRatio η)(a : T.Slice G){r : ℝ}(hr : r < Chart.small G η)(hp : 0<r)
    (U : Set (T.Slice G))(hA : MeasurableSet U)(hU : U⊆block T r a) :
      let B:= (Chart.tangent G T.Free).restrict (base T r a U)
      MeasurePreserving (coordinate T a) (B.withDensity (fun s=> ENNReal.ofReal (Chart.jacobian η s))) ((T.order G).restrict U) := by
   intro B
   let F := Homeomorph.mulRight a
   have hv : MeasurePreserving F (T.order G) (T.order G) := paid T a
   have hm := Chart.Ratio.combined (U:=T.Free) h hr hp
   let L := F ⁻¹' U
   have ht : L ⊆ Chart.chamber _ T.Free r := fun i hi=> by
      have hj : i*a * a⁻¹ ∈ Chart.chamber G T.Free r := hU (show i*a∈U from hi)
      simpa using hj
   suffices he : MeasurePreserving (Chart.expLinks G T.Free) (B.withDensity fun s=> ENNReal.ofReal (Chart.jacobian η s)) ((T.order G).restrict L) by
     have hb : MeasurePreserving F ((T.order G).restrict L) ((T.order G).restrict U) := by
        refine ⟨hv.measurable,?_⟩
        rw [show L=F ⁻¹' U from rfl, ← Measure.restrict_map F.measurable hA,hv.map_eq]
     exact hb.comp he
   refine ⟨hm.measurable,?_⟩
   have hi : MeasurableSet L := F.measurable hA
   rw [show T.order G = Chart.physical G T.Free from rfl, ← Measure.restrict_restrict_of_subset ht, ← hm.map_eq,
      Measure.restrict_map hm.measurable hi, restrict_withDensity (hm.measurable hi),Measure.restrict_restrict (hm.measurable hi)]
   rfl

variable {P : ChartRatio G}{U : Set (T.Slice G)} (h : LocalRatio P)(a : T.Slice G)
    {e t : ℝ} (he : 0<e)(hp : e< Chart.small G P)(ht : 0<t)(hu : MeasurableSet U)(H : U⊆block T e a)

/-- Accounting with the SAME multiplicative Haar. -/
def penalty (P : ChartRatio G) (a : T.Slice G) (f' : T.Slice G→ℂ) (v : AxisChart G T) :=
   (Chart.jacobian P v) • f' (coordinate T a v)

include h he hp hu H

private theorem earns {f' : T.Slice G→ℂ}(hf : Measurable f') :
    IntegrableOn f' U (T.order G) ↔ IntegrableOn (penalty T P a f') (base T e a U) (Chart.tangent G T.Free) := by
   have hm := selected T h a hp he U hu H
   simp_rw [IntegrableOn]; rw [← hm.map_eq, integrable_map_measure hf.aestronglyMeasurable hm.measurable.aemeasurable,
      MeasureTheory.integrable_withDensity_iff_integrable_smul' (Chart.Ratio.jacobian_meas h|>.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
   simp only [fun x => ENNReal.toReal_ofReal (Chart.jacobian_nonneg (U:=T.Free) (P:=P) x)]; rfl

private theorem accrued {f' : T.Slice G→ℂ}(hf : Measurable f') :
   ∫ u in U,f' u ∂T.order G = ∫ v in base T e a U, penalty T P a f' v ∂Chart.tangent G T.Free := by
   have hv := selected T h a hp he U hu H
   rw [← hv.map_eq,integral_map hv.measurable.aemeasurable hf.aestronglyMeasurable,integral_withDensity_eq_integral_toReal_smul₀
       (Chart.Ratio.jacobian_meas h |>.ennreal_ofReal |>.aemeasurable) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)];
   simp only [fun x => ENNReal.toReal_ofReal (Chart.jacobian_nonneg (U:=T.Free) (P:=P) x)]; rfl

include ht
omit h he hp hu H in
private lemma measured (hB : MeasurableSet (base T e a U)) :
    Measure.map (fun x:AxisChart G T=> t • x) ((Chart.tangent G T.Free).restrict (inside T e a U t)) =
      ENNReal.ofReal ((t^Module.finrank ℝ (AxisChart G T))⁻¹) • (Chart.tangent G T.Free).restrict (base T e a U) := by
  unfold inside; rw [← Measure.restrict_map (f:=fun x:AxisChart G T=> t • x) (by fun_prop) hB,
      Measure.map_addHaar_smul _ ht.ne',Measure.restrict_smul]
  congr; rw [abs_of_pos (by positivity)]

lemma counts {f' : T.Slice G→ℂ}(hf : Measurable f') : IntegrableOn f' U (T.order G) ↔
    IntegrableOn (fun x:AxisChart G T=> penalty T P a f' (t • x)) (inside T e a U t) (Chart.tangent G T.Free) := by
  let μ:=Chart.tangent G T.Free; let p:=penalty T P a f'; let L:= fun x:AxisChart G T=> t • x
  have hL : Continuous L := by unfold L; fun_prop
  have htC : Continuous (coordinate T a) := (coordinate_cont T).comp (f:=fun v:AxisChart G T=>(a,v)) (continuous_const.prodMk continuous_id)
  have hπ : Measurable p := ((Chart.Ratio.jacobian_meas h).smul (hf.comp htC.measurable))
  have HB : MeasurableSet (base T e a U) := (htC.measurable hu).inter (isOpen_ball.measurableSet)
  have hl := measured T a ht HB
  rw [earns T h a he hp hu H hf]; unfold IntegrableOn
  change _ ↔ Integrable (p ∘ L) _
  rw [← integrable_map_measure hπ.aestronglyMeasurable hL.measurable.aemeasurable]
  unfold L; rw [hl,MeasureTheory.integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top]

lemma procures {f' : T.Slice G→ℂ}(hf : Measurable f') :
    ∫ x : AxisChart G T in inside T e a U t, penalty T P a f' (t • x) ∂ Chart.tangent G T.Free =
      (t^Module.finrank ℝ (AxisChart G T))⁻¹ • ∫ i in U, f' i ∂T.order G := by
  let μ:=Chart.tangent G T.Free; let p:=penalty T P a f'; let L:= fun x:AxisChart G T=> t • x
  have hL : Continuous L := by unfold L; fun_prop
  have htC : Continuous (coordinate T a) := (coordinate_cont T).comp (f:=fun v:AxisChart G T=>(a,v)) (continuous_const.prodMk continuous_id)
  have hπ : Measurable p := ((Chart.Ratio.jacobian_meas h).smul (hf.comp htC.measurable))
  have HB : MeasurableSet (base T e a U) := (htC.measurable hu).inter isOpen_ball.measurableSet
  have hl := measured T a ht HB
  change ∫ x : AxisChart G T, p (L x) ∂ μ.restrict (inside T e a U t)=_
  rw [accrued T h a he hp hu H hf, ← integral_map hL.measurable.aemeasurable hπ.aestronglyMeasurable]
  unfold μ L; rw [hl,MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
end YM.RG02.Volume
