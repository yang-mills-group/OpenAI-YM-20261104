import YM.Integration.WilsonMacroscopicForwardTransfer
import YM.Push.GRID_APPROXIMATION.Many
import YM.Integration.WilsonPositionOriginalDressedQReflection

/-! The signed square of a two-date return keeps both real emitted
insertions in their one common Wilson vacuum, including all mixed terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQFourTerms
open Filter Set MeasureTheory Lattice Wilson RG Cells Push.GridApprox
open OPE.Therm PhysicalNext.Repeat.Legato WilsonMacroscopicForwardTransfer
open scoped Topology Classical
variable {G:Gauge}(R:Run G){N per i:ℕ}
local notation "A"=>R.family.path
local notation "μ" k => scene R.family.path N per k

/-- Two independent supports suffice for the common draw of the emitted
coarse pair. All fine insertions may be full true Wilson functions. -/
theorem original (hi:i+1≤N)(Q₁ Q₂:Config G (R.family.side (i+1) per)→ℂ)(qs:Envelope Q₁)(qt:Envelope Q₂)
    (L₁ L₂:Config G (R.family.side i per)→ℂ){X Y:Set (Site (R.family.side i per))}
    (hl:Interior X L₁)(hk:Interior Y L₂)(apart:Disjoint X Y):
    let step:=backTo A N per (Nat.le_succ i)
    let lower:=exterior (C:=R.family) (N:=N) (p:=per) (Nat.le_succ i)
    (∫U,(Q₁ U-step L₁ U)*(Q₂ U-step L₂ U) ∂(μ (i+1)))=
      (∫U,Q₁ U*Q₂ U ∂(μ (i+1)))-
      (∫W,lower Q₁ W*L₂ W ∂(μ i))-
      (∫W,lower Q₂ W*L₁ W ∂(μ i))+
      (∫W,L₁ W*L₂ W ∂(μ i)):=by
  intro step lower
  letI : IsProbabilityMeasure (μ (i+1)):=probability R.makes.wilson hi
  have l1:=cylinder_env hl
  have l2:=cylinder_env hk
  have a1:Envelope (step L₁):=backTo_env A N per (Nat.le_succ i) l1
  have a2:Envelope (step L₂):=backTo_env A N per (Nat.le_succ i) l2
  have mixed₁:=joint (C:=R.family) R.makes (Nat.le_succ i) hi Q₁ (qs.integrableC (μ (i+1))) L₂ l2
  have mixed₂:=joint (C:=R.family) R.makes (Nat.le_succ i) hi Q₂ (qt.integrableC (μ (i+1))) L₁ l1
  have same:step (L₁*L₂)=step L₁*step L₂:=by
    dsimp only [step]
    rw [backTo_next A N per (le_refl i),backTo_next A N per (le_refl i),backTo_next A N per (le_refl i)]
    simpa using back_factors (R.family.path.levels.blocks i per).branches l1 l2 hl.localSites hk.localSites apart (R.family.path.β N per (i+1))
  have low:=retro R.makes.wilson (Nat.le_succ i) hi (L₁*L₂) (l1.mulC l2)
  change (∫U,step (L₁*L₂) U ∂(μ (i+1)))=_ at low
  rw [same] at low
  have expand:∀U,(Q₁ U-step L₁ U)*(Q₂ U-step L₂ U)=
      Q₁ U*Q₂ U-Q₁ U*step L₂ U-Q₂ U*step L₁ U+step L₁ U*step L₂ U:=by intro U;ring
  simp_rw [expand]
  have uu:Integrable (Q₁*Q₂) (μ (i+1)):=(qs.mulC qt).integrableC (μ (i+1))
  have ud:Integrable (Q₁*step L₂) (μ (i+1)):=(qs.mulC a2).integrableC (μ (i+1))
  have du:Integrable (Q₂*step L₁) (μ (i+1)):=(qt.mulC a1).integrableC (μ (i+1))
  have dd:Integrable (step L₁*step L₂) (μ (i+1)):=(a1.mulC a2).integrableC (μ (i+1))
  have e₁:=integral_add ((uu.sub ud).sub du) dd
  have e₂:=integral_sub (uu.sub ud) du
  have e₃:=integral_sub uu ud
  simp only [Pi.mul_apply,Pi.sub_apply] at e₁ e₂ e₃ low
  rw [e₁,e₂,e₃]
  change _=(∫U,Q₁ U*Q₂ U ∂(μ (i+1)))-(∫W,exterior (C:=R.family) _ Q₁ W*L₂ W ∂(μ i))-
    (∫W,exterior (C:=R.family) _ Q₂ W*L₁ W ∂(μ i))+(∫W,L₁ W*L₂ W ∂(μ i))
  rw [mixed₁,mixed₂,low];rfl

end YM.Integration.WilsonPositionOriginalDressedQFourTerms
