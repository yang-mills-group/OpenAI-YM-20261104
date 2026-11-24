import YM.Integration.WilsonTrueProjectedBareEntrance
import YM.Integration.WilsonMeasuredOwnerZero
import YM.Integration.WilsonCapturedPrimaryCanonicalFace

/-! A common original section at the upper end of the comparison has exactly
zero boundary defect. The physical top vector can depend on both regulators. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonTrueProjectedUpperSource

open Function Filter Topology Lattice RG Labels Source
open Wilson Trace.Physical Trace.Physical.GermGraph
open Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonTrueProjectedDualHistory
open Extra.Histories WilsonTrueProjectedTwoCarrierStep WilsonMeasuredCoefficientTransport
open scoped Topology BigOperators ComplexConjugate

variable {G:Gauge} (R:Run G) {m N per k d:ℕ}
local notation "𝓒" => R.family
local notation "𝓟" j:max => (𝓒).path.rep N per j
local notation "𝓕" => (𝓒).labels.level d
local notation "𝓨" j:max => calValues (C:=𝓒) d N per j
local notation "𝓥" j:max => GermGraph.value (C:=𝓒) d N per j
local notation "𝓚" j:max => safety (𝓒) j

/-- Matching a physical section at an admitted restart costs exactly zero,
also on the separately elected original hard representation. -/
theorem matched {j:ℕ} (Ψ:∀j,Rep G ((𝓒).side j per))
    {π₀:ℕ → Layout G} {Γ:ℕ → Pace.Coin} (course:Concourse R.alloy R.kit R.T π₀ Γ m N per k Ψ)
    (ready:(𝓒).ref d≤j) (start:m≤j) (live:j≤N)
    (F:∀j,Config G ((𝓒).side j per)→ℂ) (v:(𝓕).Coeff) (head:F j=(𝓨 j) v) :
    Full R (N:=N) (d:=d) Ψ F j v 0:=by
  let e:=((𝓒).factory d N per).entries j v
  let z:=stretch (0:ℂ) e
  have input:=entryOk (C:=𝓒) d N per j R.makes ready live v
  have fz := stretch_format (0:ℂ) input.1
  have rz : z.remBound 0 (𝓟 j) (𝓚 j) 0 := by
    simpa [z] using stretch_rem (0:ℂ) input.2
  obtain ⟨param,slots,_⟩:=WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course start live
  have fΨ:=formats z (Ψ j) (𝓟 j) param.symm slots.symm fz
  have rΨ:=rent z (Ψ j) (𝓟 j) param.symm slots.symm rz
  have dims:=dimensions (C:=𝓒) d N per j R.makes ready live
  have zeroJet:=WilsonCapturedPrimaryCanonicalFace.engineering e (0:ℂ) dims.1 dims.2 input.1 input.2
  have vac : (𝓟 j).p=plank (𝓒) j := (R.makes.wilson.represents N per j live).vac
  have pz : page (C:=𝓒) d per j z=0 := by
    unfold page
    rw [←vac]
    simpa [z] using zeroJet
  refine ⟨z,z,0,0,⟨fz,rz⟩,pz,⟨fΨ,rΨ⟩,by simp,?_⟩
  rw [head,sub_self,WilsonMeasuredOwnerZero.field rΨ,add_zero]
  funext U
  change (stretch (0:ℂ) e).density 0 _ _ U=0
  rw [stretch_density,zero_mul]

/-- The original microscopic Wilson field is its raw section multiplied by
the full bare vacuum on all fields. No size restriction is imposed on the
cutoff-dependent fitted vector. -/
theorem bare (Ψ:∀j,Rep G ((𝓒).side j per))
    {π₀:ℕ → Layout G} {Γ:ℕ → Pace.Coin} (course:Concourse R.alloy R.kit R.T π₀ Γ m N per k Ψ)
    (ready:(𝓒).ref d≤N) (start:m≤N)
    (F:∀j,Config G ((𝓒).side j per)→ℂ) (raw:(𝓕).Coeff)
    (head:∀U,F N U=((Ψ N).eval U:ℂ)*((𝓒).localSection d).places raw 0 U) :
    Full R (N:=N) (d:=d) Ψ F N ((𝓕).scaled ((𝓒).path.levels.clock.threshold N) raw) 0:=by
  apply matched R Ψ course ready start le_rfl F
  funext U
  let θ:=(𝓒).path.levels.clock.threshold N
  let v:=(𝓕).scaled θ raw
  have top := (R.makes.calibrated d N per ready).encode v U
  have quiet : (Ψ N).eval U=(𝓟 N).eval U := congrFun (course.1.walk N start le_rfl).view U
  have heat : θ≠0:=(plank (𝓒) N).threshold_pos.ne'
  have unscaled : (𝓕).scaled θ⁻¹ v=raw:=by
    simpa only [inv_inv] using ((𝓕).scaled_inv (inv_ne_zero heat) raw)
  apply Eq.trans (head U)
  rw [quiet]
  apply Eq.trans _ top.symm
  unfold Source.initial
  change ((𝓟 N).eval U:ℂ)*((𝓒).localSection d).places raw 0 U =
    (((𝓒).S.a N:ℂ)^d)*((𝓟 N).eval U:ℂ)*
      ((((𝓒).S.a N:ℂ)^d)⁻¹*((𝓒).localSection d).places ((𝓕).scaled θ⁻¹ v) 0 U)
  rw [unscaled]
  have sep:((𝓒).S.a N:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ((𝓒).S.a_pos N).ne'
  field_simp


/-- Three physical ways of starting the comparison. At the ultraviolet
cutoff, the actual raw vector is supplied in the original link coordinates. -/
def Launch (d N : ℕ) (Ψ:∀j,Rep G ((𝓒).side j per)) (F:Spaces R per) (j:ℕ) (total:ℝ) : Prop :=
  (∃ (a:store (𝓒) d per j) (B:ℝ), Admitted R Ψ j a B ∧ ((𝓒).labels.level d).coeffSize a.x≤B ∧
     F j=a.density 0 ((𝓒).localSection d) (Ψ j) ∧ total=(2+4*stock (𝓒) j)*B) ∨
  total=0 ∧ ((∃ v:(𝓒).label d, F j=calValues (C:=𝓒) d N per j v) ∨
     j=N ∧ ∃ raw:(𝓒).label d, ∀U,F N U=((Ψ N).eval U:ℂ)*((𝓒).localSection d).places raw 0 U)

theorem admitted (Ψ:∀j,Rep G ((𝓒).side j per))
    {π₀:ℕ → Layout G} {Γ:ℕ → Pace.Coin} (course:Concourse R.alloy R.kit R.T π₀ Γ m N per k Ψ)
    {j:ℕ} (start:m≤j) (live:j≤N) (ready:Opened (𝓒) d j per)
    (F:Spaces R per) {total:ℝ} (launch:Launch R d N Ψ F j total) :
    ∃v,Full R (N:=N) (d:=d) Ψ F j v total := by
  rcases launch with ⟨a,B,paid,co,head,rfl⟩ | ⟨rfl,fit | raw⟩
  · exact WilsonTrueProjectedBareEntrance.original R π₀ Γ Ψ course start live ready F a paid co head
  · obtain ⟨v,head⟩:=fit
    exact ⟨v,matched R Ψ course ready.post start live F v head⟩
  · obtain ⟨rfl,v,head⟩:=raw
    exact ⟨_,bare R Ψ course ready.post start F v head⟩

end YM.Integration.WilsonTrueProjectedUpperSource
