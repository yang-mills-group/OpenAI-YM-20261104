import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFullSingletonIdentity
import YM.Next.MULTISOURCE.First
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! At a genuine posting date, compare two choices of a freshly inserted
ordinary source on the very same (possibly already marked) old density.
Even an unbounded old singleton cancels from their normalized difference.
Its quiet coefficient is the original vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Extra.Trajectories
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V]{C:Census V}

theorem posted_physical_increment (old:Poly C)(ρ:ℝ)(positive:0<ρ)(quiet:old.part C.quiet=(ρ:ℂ))
    (u v:V→ℂ)(a:V)(w:ℝ):
    let post:=fun source:V→ℂ=>Poly.pass (∑i:V,Poly.send (C.fire i) (source i))*old
    (w:ℂ)*(((ρ:ℂ)⁻¹ • post u).part (C.fire a))-(w:ℂ)*(((ρ:ℂ)⁻¹ • post v).part (C.fire a))=
      (w:ℂ)*(u a-v a):=by
  intro post
  have raw (z:V→ℂ):(post z).part (C.fire a)=old.part (C.fire a)+z a*(ρ:ℂ):=by
    change (_*old).part (C.fire a)=_
    rw [Multi.first_mul,pass_fire,pass_fire,quiet]
    simp [Census.quiet,Census.fire]
  rw [Poly.part_smul,Poly.part_smul,raw,raw]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

theorem posted_quiet_current {G:Gauge}{n:Side}{T I:Type}{o:V→Site n}{P:Rep G n}
    (A:QuadraticLocal.Gallery T I o P C)(t₀ t₁:T)(w:V→ℝ)(a:V)
    (old:Config G n→Poly C)(u v:Config G n→V→ℂ)(live:∀U,0<P.eval U)
    (quiet:∀U,(old U).part C.quiet=(P.eval U:ℂ))
    (posted:∀U,A.density t₁ U=Poly.pass (∑i:V,Poly.send (C.fire i) (u U i))*old U)
    (prior:∀U,A.density t₀ U=Poly.pass (∑i:V,Poly.send (C.fire i) (v U i))*old U)(U:Config G n):
    (w a:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t₁ U).part (C.fire a))-
      (w a:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t₀ U).part (C.fire a))=(w a:ℂ)*(u U a-v U a):=by
  rw [posted,prior]
  exact posted_physical_increment (old U) (P.eval U) (live U) (quiet U) (u U) (v U) a (w a)

end YM.Integration.FVA1Physical.Exchange.RoseCut
