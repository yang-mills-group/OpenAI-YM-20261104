import YM.Integration.WilsonCenteredMixedSetFiling
import YM.Integration.WilsonCenteredHardSetRead
import YM.Integration.WilsonCenteredHardFiled

/-! Hear the full mixed face on the original Wilson fields after the actual
owners are filed. The remaining exterior and the original quiet gas stay in
the same outer sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMixedSetRead
open Finset RG Lattice Wilson Marker QuadraticLocal Planned.GuardedAtom Push.Local Source Labels Extra.Histories
open WilsonCenteredOccupiedHardSets WilsonCenteredSoftInventory WilsonCenteredMixedSetFiling
open WilsonCenteredHardSetRead WilsonCenteredHardSetFiling WilsonCenteredHardAnswers
open WilsonCenteredFiledAtoms
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} {Z : Support n} {Q : Config G n→ℂ} {b : ℝ} (E : Receipt P Z Q b)
    (H : Hard X P.p P.activities.forced P.activities.K o R) (K : Guard.Keeper P.p P.activities)

theorem grouped (s : R.Mode) (live : s≠R.quiet) (x : X) (U : Config G n)
    (serial : (E.Row×Chosen)×Finset ℕ ↪ ℕ) {b' v : ℝ}
    (due : ForceCost P.p P.activities (placed E H K s x serial) b') (quiet : P.activities.KBound P.p v)
    (old : Summable (Fusion.Attached.packet P.activities P.p (H.hard x) U)) :
    WilsonCenteredHardAnswers.read (P:=P) (placed E H K s x serial) U = Q U*(WilsonCenteredAbsoluteHard.gas H x U).part s :=by
  have law : HasSum (fun F=>(Fusion.Attached.packet P.activities P.p (H.hard x) U F).part s)
      ((WilsonCenteredAbsoluteHard.gas H x U).part s) := (Poly.get _).hasSum old.hasSum
  rw [←(law.mul_left (Q U)).tsum_eq]
  unfold WilsonCenteredHardAnswers.read placed
  apply (WilsonCenteredOccupiedHardRead.original (P:=P) (fun a : E.Row×Chosen=>E.ground a.1)
    (fun a=>a.2.val) U K serial (sample E H s x) (fun a=>a.2.property) due quiet).trans
  apply tsum_congr
  intro F
  rw [WilsonCenteredHardSetRead.collection H s live x U F]
  by_cases permitted : P.activities.admissible P.p U F
  · simp only [if_pos permitted]
    have hardSum : Summable (fun I : Chosen=>contribution H s x U F I.val) := by
      apply summable_of_ne_finset_zero (s:=F.powerset.subtype (fun I=>I.Nonempty))
      intro I missing
      have absent : ¬I.val⊆F :=by simpa using missing
      simp [contribution,absent]
    rw [←(E.posted U).tsum_eq,tsum_mul_tsum_of_summable_norm (E.posted U).summable.norm hardSum.norm]
    apply tsum_congr
    intro a
    by_cases present : a.2.val⊆F <;> simp [WilsonCenteredMixedSetFiling.sample,reading,word,contribution,present,mul_assoc]
  simp [permitted]

include E K in
theorem original {d : ℕ} {F : Frame G d} (S : SectionData F) (Y : Hol G) (s : R.Mode)
    (live : s≠R.quiet) (x : X) (y : Site n) (center : y∈Z) (resident : ∀v∈s.val,o v∈Z)
    (law : P.activities.ForcedFamily P.p) (w : V→ℝ) (hw : ∀v,0<w v) {κ v : ℝ} (div : 0<κ)
    (paid : H.Paid w P.p.B P.p.supportExponent κ) (vac : P.activities.KBound P.p v)
    (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (old : ∀U,Summable (Fusion.Attached.packet P.activities P.p (H.hard x) U)) :
    Store P S Y y κ ((price b w s κ+(hitWidth P.p*v)*price b w s κ)/κ)
      (fun U=>(Real.exp (P.exponent U):ℂ)*(Q U*(WilsonCenteredAbsoluteHard.gas H x U).part s)) :=by
  letI : Countable E.Row := E.counted
  letI := Encodable.ofCountable ((E.Row×Chosen)×Finset ℕ)
  let serial : (E.Row×Chosen)×Finset ℕ ↪ ℕ := ⟨Encodable.encode,Encodable.encode_injective⟩
  obtain ⟨format,cost⟩:=WilsonCenteredMixedSetFiling.original E H K s x y center resident serial law w hw paid vac hv room
  obtain ⟨q,fit,debt,identity⟩:=WilsonCenteredHardFiled.source S Y y div (placed E H K s x serial) format cost
  refine ⟨q,fit,debt,fun U=>?_⟩
  exact (identity U).trans (congrArg (fun z=>(Real.exp (P.exponent U):ℂ)*z)
    (grouped E H K s live x U serial cost vac (old U)))

end YM.Integration.WilsonCenteredMixedSetRead
