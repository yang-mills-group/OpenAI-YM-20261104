import YM.Integration.WilsonPositionOriginalDressedQPathSquare

/-! The joined Wilson expectation of all four reflected terms is taken on
one path and one older marginal, including all the old vacuum effects. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPosterior
open Lattice Wilson RG Cells Set MeasureTheory ProbabilityTheory Function
open OPE.Therm PhysicalNext.Repeat.Legato QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDressedQFailedPath
open scoped Classical Topology
variable {G:Gauge}(R:Run G){N per i:ℕ}
open private pulled from YM.Integration.WilsonPositionOriginalDressedQPathHearing
open private same from YM.Integration.WilsonPositionOriginalDressedQPathSquare

theorem conditional (live:i<N)(Q:Config G (R.family.side (i+1) per)→ℂ)(paid:Envelope Q):
    Envelope (exterior (C:=R.family) (p:=per) (N:=N) (Nat.le_succ i) Q):=by
  let K:=next R.family N per i
  letI:IsMarkovKernel K:=isMarkov R.family R.makes live
  rw [show exterior (C:=R.family) (p:=per) (N:=N) (Nat.le_succ i) Q=(fun W=>∫U,Q U ∂K W) from
    funext fun W=>(WilsonPositionOriginalDressedQFibre.measured R live Q W).symm]
  obtain ⟨b,fee⟩:=paid.cost
  exact ⟨(paid.meas.stronglyMeasurable.integral_kernel (κ:=K)).measurable,b,
    fun W=>by simpa using norm_integral_le_of_norm_le_const (ae_of_all (K W) fee)⟩

theorem full (live:i<N)(Q₁ Q₂:Config G (R.family.side (i+1) per)→ℂ)(qs:Envelope Q₁)(qt:Envelope Q₂)
    (L₁ L₂:Config G (R.family.side i per)→ℂ)(ll:Envelope L₁)(lr:Envelope L₂):
    (∫ω:ConfigurationPath R per,(Q₁ (ω (i+1))-L₁ (ω i))*(Q₂ (ω (i+1))-L₂ (ω i)) ∂path R.family R.makes N per)=
      ∫W,exterior (C:=R.family) (N:=N) (Nat.le_succ i) (fun U=>Q₁ U*Q₂ U) W-
          exterior (C:=R.family) (N:=N) (Nat.le_succ i) Q₁ W*L₂ W-
          exterior (C:=R.family) (N:=N) (Nat.le_succ i) Q₂ W*L₁ W+L₁ W*L₂ W ∂scene R.family.path N per i:=by
  let law:=path R.family R.makes N per
  let ν:=scene R.family.path N per i
  letI:IsProbabilityMeasure law:=path_probability R.family R.makes N per
  letI:IsProbabilityMeasure ν:=probability (H:=R.family.path) (p:=per) R.makes.wilson live.le
  let χ:ConfigurationPath R per → Config G (R.family.side (i+1) per):=fun ω=>ω (i+1)
  let ψ:ConfigurationPath R per → Config G (R.family.side i per):=fun ω=>ω i
  have q₁:Envelope (Q₁ ∘ χ):=pulled qs (measurable_pi_apply _)
  have q₂:Envelope (Q₂ ∘ χ):=pulled qt (measurable_pi_apply _)
  have a₁:Envelope (L₁ ∘ ψ):=pulled ll (measurable_pi_apply _)
  have a₂:Envelope (L₂ ∘ ψ):=pulled lr (measurable_pi_apply _)
  have joined:=conditional R live (fun U=>Q₁ U*Q₂ U) (qs.mulC qt)
  have h₁:=conditional R live Q₁ qs
  have h₂:=conditional R live Q₂ qt
  have integrate {α:Type}[MeasurableSpace α](μ':Measure α)[IsFiniteMeasure μ'] {F H I J:α→ℂ}
      (hf:Envelope F)(hh:Envelope H)(hi:Envelope I)(hj:Envelope J):
      (∫x,F x-H x-I x+J x ∂μ')=(∫x,F x ∂μ')-(∫x,H x ∂μ')-(∫x,I x ∂μ')+(∫x,J x ∂μ'):=by
    have f:=hf.integrableC μ'; have h:=hh.integrableC μ'
    have i':=hi.integrableC μ'; have j':=hj.integrableC μ'
    have e₁:=integral_add ((f.sub h).sub i') j'
    have e₂:=integral_sub (f.sub h) i'
    have e₃:=integral_sub f h
    simp only [Pi.sub_apply] at e₁ e₂
    rw [e₁,e₂,e₃]
  have expand (ω:ConfigurationPath R per):
      (Q₁ (ω (i+1))-L₁ (ω i))*(Q₂ (ω (i+1))-L₂ (ω i))=
      Q₁ (ω (i+1))*Q₂ (ω (i+1))-Q₁ (ω (i+1))*L₂ (ω i)-Q₂ (ω (i+1))*L₁ (ω i)+L₁ (ω i)*L₂ (ω i):=by ring
  have pre:=integrate law (q₁.mulC q₂) (q₁.mulC a₂) (q₂.mulC a₁) (a₁.mulC a₂)
  have post:=integrate ν joined (h₁.mulC lr) (h₂.mulC ll) (ll.mulC lr)
  simp only [Function.comp_apply,χ,ψ,law] at pre
  dsimp only [ν] at post
  simp_rw [expand];rw [pre,post]
  have one:Envelope (fun _:Config G (R.family.side i per)=>(1:ℂ)):=⟨measurable_const,1,fun _=>by simp⟩
  have top:=WilsonPositionOriginalDressedQPathHearing.measured R live (fun U=>Q₁ U*Q₂ U) _ (qs.mulC qt) one
  simp only [mul_one] at top
  rw [top,WilsonPositionOriginalDressedQPathHearing.measured R live Q₁ L₂ qs lr,
    WilsonPositionOriginalDressedQPathHearing.measured R live Q₂ L₁ qt ll,
    same R live.le (fun W=>L₁ W*L₂ W) (ll.meas.mul lr.meas)]
end YM.Integration.WilsonPositionOriginalDressedQPosterior
