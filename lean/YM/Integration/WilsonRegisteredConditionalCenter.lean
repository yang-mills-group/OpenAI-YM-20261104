import YM.Integration.WilsonPhysicalComplexVariance

/-! The actual earlier singleton is subtracted inside each fibre.
Its fluctuation is financed by the original fine second moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredConditionalCenter
open Filter MeasureTheory ProbabilityTheory Lattice RG Wilson OPE.Therm
open scoped Classical ENNReal Topology
variable {G:Gauge} (C:Family G) {N per m:ℕ} (made:C.Makes) (live:m<N)
local notation "coarse" => Config G (C.side m per)
local notation "fine" => Config G (C.side (m+1) per)
local notation "μ" => scene C.path N per m
local notation "μf" => scene C.path N per (m+1)
local notation "K" => QLocalPhysicalPathKernel.next C N per m
local notation "ν" => WilsonRegisteredJointAxial.law C N per m
local notation "read" => actualAverage C (N:=N) (p:=per) (m:=m) (E:=ℂ)

include made live

private theorem average (B:fine→ℂ) (V:coarse): (∫U,B U ∂(K) V)=read B V:=by
  rw [QLocalPhysicalPathKernel.held C made live V]
  exact ActualWilsonConditionalRoots.average C made live V B

theorem covariance (B F:fine→ℂ) (hb:Envelope B) (hf:Envelope F) (V:coarse):
    read (fun U=>(B U-read B V)*F U) V=read (fun U=>B U*F U) V-read B V*read F V:=by
  letI:=QLocalPhysicalPathKernel.isMarkov C (p:=per) made live
  calc
    _ = ∫U,B U*F U-(read B V)*F U ∂(K) V:=by
      rw [←average C made live _ V];congr 1;funext U;ring
    _ = (∫U,B U*F U ∂(K) V)-read B V*(∫U,F U ∂(K) V):=by
      rw [integral_sub ((hb.mulC hf).integrableC ((K) V)) ((hf.integrableC ((K) V)).const_mul _),integral_const_mul]
    _ = _:=by rw [average C made live _ V,average C made live F V]

theorem income (B:fine→ℂ) (hb:Envelope B):
    let H:=fun w:coarse×fine=>B w.2-read B w.1
    MemLp H 2 ν ∧ (∫w,‖H w‖^2 ∂ν) ≤ ∫U,‖B U‖^2 ∂μf:=by
  intro H
  letI:IsProbabilityMeasure μ:=probability made.wilson live.le
  letI:IsFiniteMeasure μ:=⟨by rw [measure_univ];norm_num⟩
  letI:SigmaFinite μ:=IsFiniteMeasure.toSigmaFinite _
  letI:SFinite μ:=inferInstance
  letI:=QLocalPhysicalPathKernel.isMarkov C (p:=per) made live
  letI:IsProbabilityMeasure ν:=by change IsProbabilityMeasure ((μ) ⊗ₘ (K));infer_instance
  letI:IsFiniteMeasure ν:=⟨by rw [measure_univ];norm_num⟩
  obtain ⟨c,cap⟩:=hb.cost
  have mean : Measurable (read B):=by
    have eq:(fun V=>∫U,B U ∂(K) V)=read B:=funext (average C made live B)
    rw [←eq]
    exact (hb.meas.stronglyMeasurable.integral_kernel (κ:=K)).measurable
  have bound (V:coarse):‖read B V‖≤c:=by
    rw [←average C made live B V]
    simpa using (norm_integral_le_of_norm_le_const («μ»:=(K) V) (ae_of_all _ cap))
  have measured:Measurable H:=(hb.meas.comp measurable_snd).sub (mean.comp measurable_fst)
  have hH:MemLp H 2 ν:=MemLp.of_bound measured.aestronglyMeasurable (c+c) (ae_of_all _ fun w=>
    (norm_sub_le _ _).trans (add_le_add (cap w.2) (bound w.1)))
  have hv (V:coarse):MemLp B 2 ((K) V):=MemLp.of_bound hb.meas.aestronglyMeasurable c (ae_of_all _ cap)
  letI:IsProbabilityMeasure μf:=probability made.wilson live
  have hb2:MemLp B 2 μf:=MemLp.of_bound hb.meas.aestronglyMeasurable c (ae_of_all _ cap)
  have snd:=WilsonRegisteredJointAxial.fine C made live (per:=per)
  have b2:Integrable (fun w:coarse×fine=>‖B w.2‖^2) ν:=(hb2.comp_measurePreserving snd).norm.integrable_sq
  have marginal:Integrable (fun V=>∫U,‖B U‖^2 ∂(K) V) μ:=by
    have h:=((Measure.integrable_compProd_iff («μ»:=μ) (κ:=K) b2.aestronglyMeasurable).mp b2).2
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using h
  refine ⟨hH,?_⟩
  calc
    _ = ∫V,∫U,‖B U-read B V‖^2 ∂(K) V ∂μ:=Measure.integral_compProd («μ»:=μ) (κ:=K) hH.norm.integrable_sq
    _ ≤ ∫V,∫U,‖B U‖^2 ∂(K) V ∂μ:=by
      apply integral_mono_of_nonneg (ae_of_all _ fun V=>integral_nonneg fun U=>sq_nonneg _) marginal
      apply ae_of_all
      intro V
      change (∫U,‖B U-read B V‖^2 ∂(K) V) ≤ ∫U,‖B U‖^2 ∂(K) V
      rw [←average C made live B V,WilsonPhysicalComplexVariance.original (hv V)]
      exact sub_le_self _ (sq_nonneg _)
    _ = ∫w:coarse×fine,‖B w.2‖^2 ∂ν:=(Measure.integral_compProd («μ»:=μ) (κ:=K) b2).symm
    _ = _:=by
      rw [←snd.map_eq,integral_map snd.measurable.aemeasurable (hb.meas.norm.pow_const 2).aestronglyMeasurable]

end YM.Integration.WilsonRegisteredConditionalCenter
