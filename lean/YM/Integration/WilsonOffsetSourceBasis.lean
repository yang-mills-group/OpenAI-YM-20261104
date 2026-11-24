import YM.Integration.WilsonOffsetConditionalCharge
import YM.FullVolume.Cross
import YM.RGComparison.Core16.Spool.Beacon

/-! Original independent colored insertions at their two true sites, with
the exact incoming coefficients and any other finite continuous probes left in place. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetSourceBasis
open Function MeasureTheory Lattice RG Wilson Source Labels Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonOffsetConditionalCharge
open scoped Classical BigOperators
variable {G:Gauge}

theorem expand {n:Side} {d:ℕ} {F:Frame G d} (B:SectionData F) (x:F.Coeff) (z:Site n) (U:Config G n) :
    B.places x z U=∑i:F.Index,x i*B.places (Pi.single i 1) z U:=by
  classical
  let ℓ : F.Coeff →ₗ[ℂ] ℂ := (MvPolynomial.aeval (Source.entry (expandAt z U))).toLinearMap.comp B.evalC
  have all : x=∑i:F.Index,x i • (Pi.single i 1:F.Coeff):=by
    ext k
    simp [Finset.sum_apply,Pi.single_apply]
  change ℓ x=∑i:F.Index,x i*ℓ (Pi.single i 1)
  conv_lhs => rw [all]
  simp [smul_eq_mul]

theorem birth (R:Run G) {m p d:ℕ} (hr:R.family.ref d ≤ m+1) (z:Site (R.family.side (m+1) p))
    (v:R.family.label d) (U:Config G (R.family.side (m+1) p)) :
    let S:=R.family.path.levels.clock.op m p
    let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (m+1))⁻¹ v
    forward R.makes (N:=m+1) (Nat.lt_succ_self m) z v U =
      ∑i:(R.family.labels.level d).Index,x i*
        ((Next.Foundations.localSection G d).places (Pi.single i 1) z U-
        (Next.Foundations.localSection G d).places (Pi.single i 1) (S.ratio.embed (S.ratio.parent z)) U) :=by
  rw [born_difference R.makes hr z v U]
  dsimp only
  rw [expand,expand]
  simp only [mul_sub,Finset.sum_sub_distrib]
  rfl

private theorem weighted {c f:Side} {S:StepData c f} {P:Rep G f} (hk:S.IsKernel P.beta G)
    (hp:Envelope P.eval) (V:Config G c) (X:Config G f→ℂ) (hx:Continuous X) :
    Integrable (fun U=>S.density P.beta U V • ((P.eval U:ℂ)*X U)) (prior G f) :=
  StepData.push_slice hk V _ (((Envelope.ofReal_env hp).mulC (Envelope.compactC hx)).integrableC (prior G f))

theorem combination {ι:Type*} [Fintype ι] {c f:Side} {S:StepData c f} {P:Rep G f}
    (hk:S.IsKernel P.beta G) (hp:Envelope P.eval) (V:Config G c) (x:ι→ℂ)
    (X:ι → Config G f→ℂ) (hx:∀ i,Continuous (X i)) :
    conditional S P V (fun U=>∑i,x i*X i U)=∑i,x i*conditional S P V (X i) :=by
  classical
  let Z (i:ι) (U:Config G f):=S.density P.beta U V • ((P.eval U:ℂ)*X i U)
  have wi (i:ι): Integrable (Z i) (prior G f):=weighted hk hp V _ (hx i)
  have form : (fun U=>S.density P.beta U V • ((P.eval U:ℂ)*∑i,x i*X i U)) =
      fun U=>∑i,x i*Z i U:=by
    funext U
    simp only [Z,Complex.real_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [conditional,StepData.push]
  rw [form,integral_finsetSum _ (fun i _=>(wi i).const_mul _),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  ring

end YM.Integration.WilsonOffsetSourceBasis
