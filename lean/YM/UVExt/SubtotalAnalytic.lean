import YM.UVExt.TraceShape
import YM.UVExt.QuadField
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay
open RG Wilson Lattice Tree Pressure ConnectedActivityE6 Coat Raw Mask Pulse Itinerary Poll Pond Gaussian MeasureTheory Measure
open Filter Set Function Metric Push.AbsoluteSums Matter Traces
open scoped Topology BigOperators Classical ENNReal

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (X:Coat T F) (R:Rep G f) (t:ℝ) (Ñ:Precision.ChartRatio G) (l : Finset ℕ) (d:ℕ) (W:ℝ) (p:Molecule S)
variable {μ cst:ℝ} {L:Side} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {o:Target.Order G W}

open Finset

def people : Finset (Unit⊕Head S) := ({()}:Finset Unit).disjSum p
def wages (w:Iris X R d p) := Sum.elim (fun _:Unit=>mist X R d p w) (shade X R t Ñ l d W p w)
lemma printed_sum (w:Iris X R d p) (z:ℂ) : tiltedTerm X R t Ñ l d W p w z = Traces.bundled (people p) (wages X R t Ñ l d W p w) z := by simp [tiltedTerm, Traces.bundled,people,wages, Finset.prod_disjSum]
lemma products_uniform (i:Unit ⊕ Head S) : Traces.UniformForm (fun w=>(wages X R t Ñ l d W p w) i) := by
 rcases i with _|s
 · refine Or.inl ⟨Fintype.card (slice X R d p), fun _=>?pp⟩; rw [Fintype.card_coe]; exact ⟨_,_,rfl⟩
 rcases s with A|j|j|j
 · exact Or.inl ⟨seedPower X A, fun _=> ⟨_,_,rfl⟩⟩
 · exact Or.inl ⟨0, fun _=> ⟨_,_,rfl⟩⟩
 · simp only [Traces.UniformForm,wages,shade,capsule,Sum.elim]
   by_cases h:(isHotTag j)=true
   · exact Or.inr fun _ => ⟨_,if_pos h⟩
   · exact Or.inl ⟨0,fun _=> ⟨_,_,if_neg h⟩⟩
 exact Or.inl ⟨0,fun _=> ⟨_,_,rfl⟩⟩

variable (hk : X.width=o.K) (hx : 0<R.beta)
variable (H:Cash W X.x μ L Q o cst T R)
abbrev allow (r:ℝ) := Cash W X.x μ L Q o cst T (scaled R r)

include hk hx
set_option maxHeartbeats 300000 in
omit hx hk in
lemma wage_mist {r:ℝ} (hr:0<r) : Measurable (fun w:Iris X R d p=> (mist X R d p w).run r) := by
 rw [show (fun w=>(mist X R d p w).run r)=fun (w:Iris X R d p)=> Complex.ofReal (Gaussian.tilt (minor X R d p) r w.2) from funext fun w=>fog X R d p w r hr]
 apply Complex.measurable_ofReal.comp
 apply Measurable.mul measurable_const; apply Measurable.exp; exact measurable_const.mul ((Gaussian.value_cont (minor X R d p)).measurable.comp (measurable_snd (β:=Eye X R d p) (α:=F.Slice G)))

set_option maxHeartbeats 200000 in
lemma wage_head (i : Head S) {r:ℝ} (hr:0<r) (hA: allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o) r) : Measurable (fun w:Iris X R Q.halo p=> (shade X R o.a Q.table l Q.halo W p w i).run (r:ℝ)) := by
 let π (w:Iris X R Q.halo p):=(w.1,√r • spill (slice X R Q.halo p) w.2)
 have hpπ : Measurable π := measurable_fst.prodMk (((spill_m (slice X R Q.halo p)).comp (measurable_snd (α:=F.Slice G) (β:=Eye X R Q.halo p))).const_smul (Real.sqrt r))
 let hEq : (fun w:Iris X R Q.halo p=> (shade X R o.a Q.table l Q.halo W p w i).run (r:ℝ)) = Complex.ofReal ∘ ((fun j=>(X.wrapY j.1).vertex (scaled R r) Q.table W o.a l Q.halo j.2 i) ∘ π) := funext (fun w=> restores _ _ _ _ _ _ hr hx Q.table_exists.scale.ne' i)
 exact hEq ▸ Complex.measurable_ofReal.comp (Measurable.comp (body_m X _ l _ hA hk i) hpπ)

lemma wages_m (i:Unit ⊕ Head S) {r:ℝ} (hr:0<r) (hA: allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o) r) : Measurable (fun w:Iris X R Q.halo p=> (wages X R o.a Q.table l Q.halo W p w i).run r) := by
 rcases i with _|i
 · exact wage_mist X R Q.halo p (r:=r) hr
 exact wage_head X R l W p hk hx i hr hA

local notation "A" => allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o)
local notation "m" => quarry X R Q.halo p
set_option maxHeartbeats 1000000
local notation "E" => Iris X R Q.halo p
local notation "K" => Eye X R Q.halo p
local notation "g" => tiltedTerm X R o.a Q.table l Q.halo W p

theorem term_m {r s:ℝ} (hr:0<r) (hs:0<s) (H₁:A r) (H₂:A s) (h:r≠s) (z:ℂ) : Measurable (fun w:E => g w z) := by
 have hf (i:Unit⊕ Head S) := UniformForm.sample _ (products_uniform X R o.a Q.table l Q.halo W p i) hr hs h (wages_m X R l W p hk hx i hr H₁) (wages_m X R l W p hk hx i hs H₂) z
 simp_rw [printed_sum,Traces.bundled]
 exact Finset.measurable_fun_prod _ fun i _=> hf i

private lemma bob {r:ℝ} (h : K→ℂ) (hr:0<r) (H₀:A r) (hX:X.manifest) :
    (∫ u,(Gaussian.tilt (minor X R Q.halo p) r u:ℝ)*h (√r • u) ∂(Pond.arch (slice X R Q.halo p) X.relating)) = ∫ u,h u ∂(Pond.arch (slice X R Q.halo p) X.relating) := by exact Gaussian.integral_tilt _ (minor_pd X _ _ _ hk H₀ hX) r hr h
variable (hX:X.manifest)
include hX
omit hx hk hX in
private lemma ofReal_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f:Ω→ℝ) : Complex.ofReal (∫ x,f x ∂μ)=∫ x,Complex.ofReal (f x) ∂μ := integral_ofReal.symm

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 500000 in
lemma tilted_real {r:ℝ} (hr:0<r) (H₀:A r) : Integrable (fun w=>g w (r:ℂ)) m ∧ subtotal X R o.a Q.table l Q.halo W p r=(X.attains (scaled R r) Q.table W o.a l Q.halo p : ℝ) ∧ ∫ w:E, ‖g w (r:ℂ)‖ ∂m ≤ ∏ i∈ p, H₀.text i := by
 let old := sterile X R o.a Q.table l Q.halo W p r
 letI : IsProbabilityMeasure (F.order G):=by unfold Forest.order; infer_instance
 letI : SFinite (F.order G):=by infer_instance
 let U := Pond.arch (slice X R Q.halo p) X.relating
 have hU := sterile_m X R l W p hk H₀
 have hI := sterile_integrable X R l W p hk H₀ hX
 let new (w:E) := (tilt (minor X R Q.halo p) r w.2:ℝ)*(old (w.1,√r •w.2):ℝ) -- expect ℝ
 have hf : (fun w:E=>g w r)= (fun w:E=> (new w:ℂ)) := funext fun w=> on_real _ _ _ _ _ _ _ _ _ _ hr hx Q.table_exists.scale.ne'
 have hv : Measurable new := by
    unfold new; apply Measurable.mul _ (hU.comp (measurable_fst.prodMk _)); exact (Continuous.measurable (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ((Gaussian.value_cont _).comp continuous_snd))))); exact (measurable_snd (α:=F.Slice G) (β:=Eye X R Q.halo p)).const_smul (Real.sqrt r)
 have hb (s) : Complex.ofReal (∫ u,new (s,u) ∂U)= Complex.ofReal (∫ u,old (s,u) ∂U) := by
    rw [ofReal_int U,ofReal_int U]; simp only [new,Complex.ofReal_mul]; exact bob X R W p hk hx (h:=fun u=>(old (s,u):ℂ)) hr H₀ hX -- argument order
 have hb := fun s=> Complex.ofReal_injective (hb s)
 have hn (s): Complex.ofReal (∫ u,‖new (s,u)‖ ∂U)=Complex.ofReal (∫ u,‖old (s,u)‖ ∂U) := by
    simp_rw [Real.norm_eq_abs,new,abs_mul,abs_of_nonneg (Gaussian.tilt_nn _ _ _),ofReal_int U,Complex.ofReal_mul]; exact bob X R W p hk hx (h:=fun u=>Complex.ofReal |old (s,u)|) hr H₀ hX
 have hn := fun s=> Complex.ofReal_injective (hn s)
 have hz := (integrable_prod_iff hI.aestronglyMeasurable).mp hI
 have hJ : Integrable new m := by
    refine (integrable_prod_iff hv.aestronglyMeasurable).mpr ⟨hz.1.mono fun x hx=>?_,by convert hz.2 using 1; exact funext hn⟩
    have ht := integrable_tilt _ (minor_pd X _ _ _ hk H₀ hX) r hr (fun z=>((old (x,z):ℝ):ℂ)) ((Complex.measurable_ofReal.comp hU).comp (measurable_const.prodMk measurable_id)) hx.ofReal
    apply Integrable.congr ht.re; exact Eventually.of_forall fun _ => by change ((↑(_)* ↑(_) : ℂ)).re = (_:ℝ); rw [← Complex.ofReal_mul, Complex.ofReal_re]
 let π:= project X R Q.halo p; let v := (F.order G).prod X.dice
 have he : (old∘π)=X.body (scaled R r) Q.table W o.a l Q.halo p := funext fun x=>cut_sweeps X (scaled R r) _ _ _ H₀ hk x
 have hh : MeasurePreserving π v m := projecting X (scaled R r) Q.halo W p H₀ hk hX
 rw [hf]
 refine ⟨hJ.ofReal,?_,?_⟩
 · unfold subtotal; rw [hf,←ofReal_int m,attains,← he]
   generalize hah: (old ∘ π) = oldX
   rw [show (∫ i,oldX i ∂(F.order G).prod X.dice)=∫ w,old w ∂m from (by rw [← hah]; exact (eq_comm.mp (hh.map_eq ▸ (MeasureTheory.integral_map (f:=old) hh.measurable.aemeasurable hU.aestronglyMeasurable))))]
   congr 1; rw [integral_prod (μ:=F.order G) (ν:=U) new hJ,integral_prod (μ:=F.order G) (ν:=U) old hI]; simp_rw [hb]
 have hbNorm w : ‖g w (r:ℂ)‖=‖(new w:ℂ)‖ := congr_arg norm (congr_fun hf w)
 simp_rw [hbNorm]
 change (∫ w, ‖(new w:ℂ)‖ ∂m) ≤ _
 simp_rw [Complex.norm_real]
 have hs := H₀.statements X rfl hk hX l p
 rw [← he] at hs
 let f' := fun w=>‖old w‖
 change ∫ i,f' (π i) ∂v ≤ _ at hs
 have hrw := (MeasureTheory.integral_map (μ:=v) (f:=f') hh.measurable.aemeasurable hU.norm.aestronglyMeasurable)
 change (∫ i,f' i ∂Measure.map π v)= _ at hrw
 rw [hh.map_eq] at hrw
 rw [← hrw] at hs
 refine le_trans ?_ hs
 apply le_of_eq; rw [integral_prod (μ:=F.order G) (ν:=U) _ hJ.norm,integral_prod (μ:=F.order G) (ν:=U) _ hI.norm]; simp_rw [hn]; rfl

lemma angular_bill {r s:ℝ} (z:ℂ) (hr:0<z.re) (hs:0<s) (H₁:A z.re) (H₂:A s) (h:z.re≠s) : ‖subtotal X R o.a Q.table l Q.halo W p z‖ ≤ (‖z‖/z.re)^ fees X R Q.halo p * ∏ i∈p,H₁.text i := by
  let f₀ w:= g w z; let f₁ w:=g w z.re
  let k:=(‖z‖/z.re)^ fees X R Q.halo p; have hk₀:0≤k := by unfold k; positivity
  have hm := term_m X R l W p hk hx hr hs H₁ H₂ h z
  have hb:= covers X R o.a Q.table l Q.halo W p; obtain ⟨I,hx,M⟩:=tilted_real X R l W p hk hx hX hr H₁
  have he : Integrable f₀ m := (I.norm.const_mul k).mono hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w=> (hb w z hr).trans (le_abs_self (k * ‖f₁ w‖)))
  refine (norm_integral_le_integral_norm f₀).trans ((integral_mono he.norm (I.norm.const_mul _) (fun w=> hb w z hr)).trans ?_)
  rw [MeasureTheory.integral_const_mul]; exact mul_le_mul_of_nonneg_left M hk₀
end YM.UVExt.EnergyRay

