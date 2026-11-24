import YM.Integration.WilsonPositionOriginalDressedQPathHearing
import YM.Integration.WilsonPositionOriginalDressedQFourTerms

/-! The two reflected Wilson differences on the complete chronological law
have exactly the original upper-date self-reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPathSquare
open Lattice Wilson RG Cells Push.GridApprox OPE.Therm PhysicalNext.Repeat.Legato
open Set MeasureTheory QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDressedQFailedPath
open scoped Classical Topology
variable {G:Gauge}(R:Run G){N per i:ℕ}
open private pulled from YM.Integration.WilsonPositionOriginalDressedQPathHearing

private theorem same {j:ℕ}(hi:j≤N)(Q:Config G (R.family.side j per)→ℂ)(h:Measurable Q):
    (∫ω:ConfigurationPath R per,Q (ω j) ∂path R.family R.makes N per)=
      ∫U,Q U ∂scene R.family.path N per j:=by
  have seen:=WilsonPositionOriginalPathMarginals.observed R.family R.makes (p:=per) hi
  rw [←seen.map_eq]
  exact (integral_map seen.measurable.aemeasurable h.aestronglyMeasurable).symm

theorem original (live:i<N)(Q₁ Q₂:Config G (R.family.side (i+1) per)→ℂ)(qs:Envelope Q₁)(qt:Envelope Q₂)
    (L₁ L₂:Config G (R.family.side i per)→ℂ){X Y:Set (Site (R.family.side i per))}
    (hl:Interior X L₁)(hk:Interior Y L₂)(apart:Disjoint X Y):
    let step:=backTo R.family.path N per (Nat.le_succ i)
    (∫ω:ConfigurationPath R per,(Q₁ (ω (i+1))-L₁ (ω i))*(Q₂ (ω (i+1))-L₂ (ω i)) ∂path R.family R.makes N per)=
      ∫U,(Q₁ U-step L₁ U)*(Q₂ U-step L₂ U) ∂scene R.family.path N per (i+1):=by
  intro step
  let law:=path R.family R.makes N per
  letI:IsProbabilityMeasure law:=path_probability R.family R.makes N per
  let χ:ConfigurationPath R per → Config G (R.family.side (i+1) per):=fun ω=>ω (i+1)
  let ψ:ConfigurationPath R per → Config G (R.family.side i per):=fun ω=>ω i
  have q₁:Envelope (Q₁ ∘ χ):=pulled qs (measurable_pi_apply _)
  have q₂:Envelope (Q₂ ∘ χ):=pulled qt (measurable_pi_apply _)
  have a₁:Envelope (L₁ ∘ ψ):=pulled (cylinder_env hl) (measurable_pi_apply _)
  have a₂:Envelope (L₂ ∘ ψ):=pulled (cylinder_env hk) (measurable_pi_apply _)
  have uu:Integrable ((Q₁ ∘ χ)*(Q₂ ∘ χ)) law:=(q₁.mulC q₂).integrableC law
  have ud:Integrable ((Q₁ ∘ χ)*(L₂ ∘ ψ)) law:=(q₁.mulC a₂).integrableC law
  have du:Integrable ((Q₂ ∘ χ)*(L₁ ∘ ψ)) law:=(q₂.mulC a₁).integrableC law
  have dd:Integrable ((L₁ ∘ ψ)*(L₂ ∘ ψ)) law:=(a₁.mulC a₂).integrableC law
  have e₁:=integral_add ((uu.sub ud).sub du) dd
  have e₂:=integral_sub (uu.sub ud) du
  have e₃:=integral_sub uu ud
  simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply,χ,ψ,law] at e₁ e₂ e₃
  have expand (ω:ConfigurationPath R per):
      (Q₁ (ω (i+1))-L₁ (ω i))*(Q₂ (ω (i+1))-L₂ (ω i))=
      Q₁ (ω (i+1))*Q₂ (ω (i+1))-Q₁ (ω (i+1))*L₂ (ω i)-Q₂ (ω (i+1))*L₁ (ω i)+L₁ (ω i)*L₂ (ω i):=by ring
  simp_rw [expand];rw [e₁,e₂,e₃]
  have one:=same R (per:=per) live (fun U=>Q₁ U*Q₂ U) (qs.meas.mul qt.meas)
  have two:=same R (per:=per) live.le (fun W=>L₁ W*L₂ W) ((cylinder_env hl).meas.mul (cylinder_env hk).meas)
  rw [one,two,WilsonPositionOriginalDressedQPathHearing.measured R live Q₁ L₂ qs (cylinder_env hk),
    WilsonPositionOriginalDressedQPathHearing.measured R live Q₂ L₁ qt (cylinder_env hl)]
  exact (WilsonPositionOriginalDressedQFourTerms.original R live Q₁ Q₂ qs qt L₁ L₂ hl hk apart).symm

end YM.Integration.WilsonPositionOriginalDressedQPathSquare
