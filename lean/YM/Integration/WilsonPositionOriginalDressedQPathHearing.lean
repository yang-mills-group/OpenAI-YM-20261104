import YM.Integration.WilsonPositionOriginalDressedQFailedPath
import YM.Integration.WilsonPositionOriginalDressedQFibre

/-! The measured mixed term at two adjacent dates is a single read on the
chronological Wilson law. The marked old and emitted fields share its draw. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPathHearing
open Lattice Wilson RG MeasureTheory Function Finset Set Preorder ProbabilityTheory
open PhysicalNext.Repeat.Legato OPE.Therm QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDressedQFailedPath
open scoped Classical Topology
variable {G:Gauge}(R:Run G){N per i:ℕ}

private theorem pulled {α β:Type*}[MeasurableSpace α][MeasurableSpace β]
    {F:β→ℂ}(h:Envelope F){χ:α→β}(m:Measurable χ):Envelope (fun a=>F (χ a)):=by
  obtain ⟨c,b⟩:=h.cost
  exact ⟨h.meas.comp m,c,fun u=>b (χ u)⟩

private theorem prob {α:Type*}[MeasurableSpace α](ν:Measure α)[IsProbabilityMeasure ν]:SFinite ν:=inferInstance

theorem measured (live:i<N)(Q:Config G (R.family.side (i+1) per)→ℂ)(L:Config G (R.family.side i per)→ℂ)
    (old:Envelope Q)(lower:Envelope L):
    (∫ω:ConfigurationPath R per,Q (ω (i+1))*L (ω i) ∂path R.family R.makes N per)=
      ∫ W,exterior (C:=R.family) (N:=N) (Nat.le_succ i) Q W*L W ∂scene R.family.path N per i:=by
  let law:=path R.family R.makes N per
  let Prefix:=((j:Finset.Iic i) → Config G (R.family.side j.val per))
  let past:ConfigurationPath R per→Prefix:=frestrictLe i
  let last:Prefix → Config G (R.family.side i per):=fun t=>t ⟨i,Finset.mem_Iic.mpr le_rfl⟩
  let tomorrow:ConfigurationPath R per → Config G (R.family.side (i+1) per):=fun ω=>ω (i+1)
  let F:Prefix × Config G (R.family.side (i+1) per)→ℂ:=fun z=>Q z.2*L (last z.1)
  let μ₀:=scene R.family.path N per 0
  have h₀:IsProbabilityMeasure μ₀:=probability (H:=R.family.path) (p:=per) R.makes.wilson (Nat.zero_le N)
  letI:=h₀
  have lastOk:Measurable last:=measurable_pi_apply _
  have pastOk:Measurable past:=measurable_frestrictLe _
  have mark:Measurable tomorrow:=measurable_pi_apply _
  have Fok:Envelope F:=(pulled old measurable_snd).mulC (pulled lower (lastOk.comp measurable_fst))
  let cut:=law.map past
  let K:=steps R.family R.makes N per i
  haveI:IsProbabilityMeasure law:=path_probability R.family R.makes N per
  letI:IsProbabilityMeasure cut:=Measure.isProbabilityMeasure_map pastOk.aemeasurable
  letI:SFinite cut:=prob cut
  letI:IsMarkovKernel K:=steps_markov R.family R.makes N per i
  have joint:cut ⊗ₘ K = law.map (fun ω=>(past ω,tomorrow ω)):=by
    apply Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have inner(t:Prefix):K t=next R.family N per i (last t):=by
    simp [K,steps,hop,dif_pos live,last]
  let E:Config G (R.family.side i per)→ℂ:=fun W=>(∫U,Q U ∂next R.family N per i W)*L W
  have borel:Measurable E:=((old.meas.stronglyMeasurable.integral_kernel (κ:=next R.family N per i)).measurable).mul lower.meas
  have observed:=WilsonPositionOriginalPathMarginals.observed R.family R.makes (p:=per) live.le
  calc
    _ = ∫z,F z ∂law.map (fun ω=>(past ω,tomorrow ω)):=by
      exact (integral_map (pastOk.prodMk mark).aemeasurable Fok.meas.aestronglyMeasurable).symm
    _ = ∫t,∫u,F (t,u) ∂K t ∂cut:=by
      rw [←joint]
      exact Measure.integral_compProd (Fok.integrableC _)
    _ = ∫t,E (last t) ∂cut:=by
      apply integral_congr_ae
      filter_upwards with t
      rw [inner]
      change (∫ u, Q u * L (last t) ∂next R.family N per i (last t)) = _
      exact integral_mul_const (L (last t)) Q
    _ = ∫ω,E (ω i) ∂law:=integral_map pastOk.aemeasurable (borel.comp lastOk).aestronglyMeasurable
    _ = ∫W,E W ∂scene R.family.path N per i:=by
      rw [←observed.map_eq];exact (integral_map observed.measurable.aemeasurable borel.aestronglyMeasurable).symm
    _ = _:=by
      apply integral_congr_ae
      filter_upwards with W
      rw [show E W=(∫U,Q U ∂next R.family N per i W)*L W from rfl,WilsonPositionOriginalDressedQFibre.measured R live]

end YM.Integration.WilsonPositionOriginalDressedQPathHearing
