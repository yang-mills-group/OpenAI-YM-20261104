import YM.Pier.Lair.Travel
import YM.RG17.Pitch

/-! The actual measured tower has a single reporting-date allowance for every
member of a prescribed finite roster, before any microscopic cutoff or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredTender
open Function Filter Finset Set Extraction Spec OPE RG12 RG17 Climb Table Next.Rank Trace.Pilot
open Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
variable {F:Final C f S} {L:Layout F} {J:ℝ→FamilyBasis (C:=C) S}
variable {u:Filter (ℕ×ℕ)} (B:Mantle F u) (E:Services C f S)
variable (paid:Pier.Lair.Present F J) (pegs:Pegs B L)
variable (near:∀ᶠ r in trail,C.S.a (L.level r)≤r ∧
  r≤C.S.a (L.level r)*C.path.levels.clock.hatBeta (L.level r)^2)
local notation "β" => C.path.levels.clock.hatBeta

include E paid pegs near in
theorem entry (d:ℕ) : ∃ e:ℕ,∀ᶠ r in trail,∀ v:Free C d,∃ w:C.label d,
    mass C d (L.shift d r w)≤β (L.level r)^e*‖v‖ ∧ master L d r w=J r d v := by
  obtain ⟨k,across⟩ := Pier.Lair.across F paid d B E L.level pegs.level.growing near
  have grows := (Station.hat_rate C.path.levels E.simpleGate).comp pegs.level.growing
  let p:=SharpGram.Lenses.price d
  refine ⟨k+p+1,?_⟩
  filter_upwards [engineeringPass B L E pegs d,across,grows.eventually_ge_atTop 2]
    with r engineering comparison positive
  let b:=β (L.level r)
  let frame:=Load.tent B (L.level r) d
  intro v
  let z:=frame.symm (J r d v)
  have hpos:0≤b := (by norm_num : (0:ℝ)≤2).trans positive
  have hz : ‖z‖≤b^k*‖v‖ := by
    have hc:=comparison.left (J r d v)
    rw [LinearEquiv.symm_apply_apply] at hc
    exact hc
  obtain ⟨w,hw,hm⟩ := engineering.1 z
  refine ⟨(L.shift d r).symm w,?_,?_⟩
  · rw [LinearEquiv.apply_symm_apply]
    refine hw.trans ?_
    calc
      2*b^p*‖z‖ ≤ (b*b^p)*(b^k*‖v‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right positive (pow_nonneg hpos _)) hz (norm_nonneg _) (by positivity)
      _ = b^(k+p+1)*‖v‖ := by ring
  · unfold master
    simp_rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hm]
    rw [pegs.frame]
    exact LinearEquiv.apply_symm_apply ..

include E paid pegs near in
theorem roster {I:Type*} [Fintype I] (d:I→ℕ) (v:(i:I)→Free C (d i)) (α:ℂ) :
    ∃ h:ℕ,∀ᶠ r in trail,∃ w:(i:I)→C.label (d i),∀ i,
      master L (d i) r (w i)=J r (d i) (v i) ∧
      mass C (d i) (α • L.shift (d i) r (w i))≤β (L.level r)^h := by
  classical
  choose e tender using fun i=>entry B E paid pegs near (d i)
  have grows: Tendsto (fun r=>β (L.level r)) trail atTop :=
    (Station.hat_rate C.path.levels E.simpleGate).comp pegs.level.growing
  let H:=univ.sup e
  refine ⟨H+1,?_⟩
  filter_upwards [eventually_all.mpr tender,grows.eventually_ge_atTop 1,
    eventually_all.mpr (fun i=>grows.eventually_ge_atTop (‖α‖*‖v i‖))] with r entries one size
  choose w cost field using fun i=>entries i (v i)
  refine ⟨w,fun i=>⟨field i,?_⟩⟩
  have fee : mass C (d i) (α • L.shift (d i) r (w i))=‖α‖*mass C (d i) (L.shift (d i) r (w i)) := Extra.Histories.Size.smul _ _ _
  rw [fee]
  let b:=β (L.level r)
  have hpow : b^(e i)≤b^H := pow_le_pow_right₀ one (le_sup (f:=e) (mem_univ i))
  calc
    ‖α‖ * mass C (d i) (L.shift (d i) r (w i)) ≤ ‖α‖ * (b^(e i)*‖v i‖) :=
      mul_le_mul_of_nonneg_left (cost i) (norm_nonneg _)
    _ = b^(e i)*(‖α‖*‖v i‖) := by ring
    _ ≤ b^H*b := mul_le_mul hpow (size i) (by positivity) (pow_nonneg (zero_le_one.trans one) _)
    _ = b^(H+1) := (pow_succ b H).symm

end YM.Integration.WilsonReportingMeasuredTender
