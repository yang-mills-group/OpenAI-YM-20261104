import YM.Integration.WilsonCenteredCrossWallet
import YM.Integration.WilsonCenteredCrossedGas

/-! The original hard operand and independently seated regular mark stay
in the same actual deposited source at each Wilson field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCrossFiled
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local Push.Corrected Source Labels
open WilsonCenteredHardAnswers WilsonCenteredHardMount WilsonCenteredCrossWallet WilsonCenteredCaptureSlots
open WilsonCenteredCaptureLampRoster WilsonCenteredFiledAtoms
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (L : Lamps X ι G P.p o R) (H : Hard X P.p P.activities.forced P.activities.K o R)
    (a b : V) (Z : Support n) (K : Guard.Keeper P.p P.activities)
    (serial : (Lots L a)×Finset ℕ ↪ ℕ)

def placed (x : X) := entered P K (ground L a Z) (owner L a) serial (word L H a b x)

theorem fitted (w : V→ℝ) (hw : ∀ i,0<w i) {E κ v : ℝ}
    (width : 0≤P.p.supportExponent+2) (regular : L.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : H.Paid w P.p.B P.p.supportExponent κ) (za : o a∈Z) (zb : o b∈Z)
    (law : P.activities.ForcedFamily P.p) (quiet : P.activities.KBound P.p v) (hv : 0≤v)
    (room : hitWidth P.p*v≤1) (y : Site n) (live : y∈Z) (x : X) :
    let rent:=(Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*((w a)⁻¹*E))*((w b)⁻¹*κ)
    ForceFormat P.p P.activities y (placed L H a b Z K serial x) ∧
      ForceCost P.p P.activities (placed L H a b Z K serial x) (rent+hitWidth P.p*v*rent) := by
  intro rent
  obtain ⟨e,pos,touch,cap,cash⟩:=invoice L H a b Z w hw width regular hard za zb
  let Xz (z : Lots L a):=WilsonCenteredOriginalCaptureOwner.ground P (ground L a Z z) (owner L a z)
  have reg (z : Lots L a) : Width.LocalCharge P.p o (Xz z) (fun U=>L.frame z.1.val x U) :=
    (Shelter.Deck.locality (L:=L) x z.1.val).widen (subset_union_right.trans subset_union_left)
  have old (z : Lots L a) : Width.LocalCharge P.p o (Xz z) (H.hard x z.2) :=
    (H.locality x z.2).widen (reaches (P:=P) (ground L a Z z) (owner L a z) z.2 (mem_singleton_self _))
  constructor
  · apply WilsonCenteredOwnerIntake.formed P (ground L a Z) (owner L a) K serial (word L H a b x) y law
      (fun _=>mem_union_left _ live)
    · intro z g U;simp only [word,(reg z).gauge g U,(old z).gauge g U]
    · intro z
      have ra : Measurable (fun U=>(L.frame z.1.val x U).part (R.fire a)) :=
        (Poly.part_cont _).measurable.comp (reg z).borel
      have hb : Measurable (fun U=>(H.hard x z.2 U).part (R.fire b)) :=
        (Poly.part_cont _).measurable.comp (old z).borel
      exact ra.mul hb
    intro z U V hg hf;simp only [word,(reg z).reads U V hg hf,(old z).reads U V hg hf]
  exact WilsonCenteredOwnerIntake.cost P (ground L a Z) (owner L a) K serial (word L H a b x) e quiet hv room pos cash touch (fun z U=>cap z x U)

theorem physical (x : X) (U : Config G n) {k v : ℝ}
    (paid : ForceCost P.p P.activities (placed L H a b Z K serial x) k) (quiet : P.activities.KBound P.p v)
    (regular : Summable (fun i=>L.frame i x U)) (hard : Summable (Fusion.Attached.packet P.activities P.p (H.hard x) U)) :
    read (P:=P) (placed L H a b Z K serial x) U =
      (L.log x U).part (R.fire a)*(WilsonCenteredAbsoluteHard.gas H x U).part (R.fire b) := by
  have shots:=WilsonCenteredCaptureLampRoster.published L (R.fire a) x U regular
  have atom (j : ℕ) : (∑' i : Row L (R.fire a),word L H a b x (i,j) U)=
      (L.log x U).part (R.fire a)*(H.hard x j U).part (R.fire b) := by
    rw [←(shots.mul_right ((H.hard x j U).part (R.fire b))).tsum_eq]
    apply tsum_congr
    intro i;simp [word,Lamps.frame,Poly.part_send,i.property]
  have plain : HasSum (fun F=>(Fusion.Attached.packet P.activities P.p (H.hard x) U F).part (R.fire b))
      ((WilsonCenteredAbsoluteHard.gas H x U).part (R.fire b)) := (Poly.get _).hasSum hard.hasSum
  rw [←(plain.mul_left ((L.log x U).part (R.fire a))).tsum_eq]
  unfold WilsonCenteredHardAnswers.read placed
  apply (WilsonCenteredCrossedGas.inGas (P:=P) (ground L a Z) U K serial (word L H a b x) paid quiet).trans
  apply tsum_congr
  intro F
  by_cases valid : P.activities.admissible P.p U F
  · simp only [valid,if_true,Fusion.Attached.packet,Multi.first_of_prod,H.quiet,atom,mul_sum,mul_assoc]
  simp [valid,Fusion.Attached.packet]

end YM.Integration.WilsonCenteredCrossFiled
