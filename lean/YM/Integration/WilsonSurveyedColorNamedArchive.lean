import YM.Integration.WilsonSurveyedColorNominatedOPE
import YM.FVA2.Position.Habitat
import YM.FVA2.SteadyBooked

/-! A literal real finite combination of the fixed dimensional insertions
has the same combination of the completed poles, integrated finite parts,
and all-order physical coordinates on the very same bulk. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNamedArchive
open Function Filter MS MS.Arts MS.Motif MS.Motif.Literal MS.Land MS.Local.Physical
open MS.Hem.Mell MS.Train MS.Dock MS.Emit MS.Outlook MS.Rake
open FVA2 FVA2.Extras FVA2.O.Lives FVA2.O.Hue FVA2.Position
open scoped Classical BigOperators
variable {G : Gauge}
variable {K : Booked (Press.portDeck G)} (M : MS_Data G K)
variable {h : ℕ} (c : Package (Press.portDeck G) h)

def archive := ∑ j, (c j : ℂ) • M.marks h j
def poles := ∑ j, (c j : ℂ) • M.poles h j

theorem paid :
    comet h 0 M.bulk (∑ j, (c j : ℂ) • gloss (Literal.linear (Mob G) (K.optics h j)))
      (archive M c) (poles M c) :=
  ArchTurn.comet_t Finset.univ (fun j _ => ArchTurn.comet_s (M.markOK h j) (c j))

theorem bill (A : Box (Mob G)) (ha : A = ∑ j, c j • K.optics h j) :
    gloss (Literal.linear (Mob G) A) =
      ∑ j, (c j : ℂ) • gloss (Literal.linear (Mob G) (K.optics h j)) := by
  rw [ha,map_sum]
  funext k z
  simp only [gloss,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.coe_smul, map_smul]
  rfl

theorem deposited (a : ℝ) :
    letIn h (logMass a) (archive M c) = ∑ j, (c j : ℂ) • soloV h (logMass a) M j := by
  funext k x t
  have hp := paid M c
  have H : hereZ h (archive M c k) t (logMass a x) =
      ∑ j, c j • hereZ h (M.marks h j k) t (logMass a x) := by
    apply MS.Shine.Lift.unique (live0 (Dock.gang (hp k)).dost)
    simpa only [archive,Finset.sum_apply,Pi.smul_apply,Complex.coe_smul] using
      Park.sum_L (fun j => M.marks h j k) Finset.univ c h
        (fun j _ => (Dock.gang (M.markOK h j k)).dost) (logMass a x) t
  ext1 l
  simpa only [letIn,soloV,nameR,Archive,four,Finset.sum_apply,Pi.smul_apply,Complex.coe_smul]
    using congrFun (congrFun H 0) l

theorem basisPrice (a : ℝ) :
    many a M (Pi.single 0 c) = ∑ j, (c j : ℂ) • soloV h (logMass a) M j := by
  unfold many
  apply Finset.sum_congr rfl
  intro j _
  have onset : (fun k (_ : Unit) => (Pi.single 0 c : ℕ → Package (Press.portDeck G) h) k j) =
      (Pi.single 0 (fun _ : Unit => c j) : ℕ → Unit → ℝ) := by
    funext k u
    by_cases hk : k = 0 <;> simp [hk,Pi.single_eq_of_ne]
  rw [onset,solo_h]
  funext k
  rw [hx_holder (Nat.zero_le _),Nat.sub_zero]
  rfl

theorem coordinates (a : ℝ) (A : Box (Mob G)) (ha : A = ∑ j, c j • K.optics h j)
    {p Y Q} (H : Determined h (Literal.linear (Mob G) A) M a p Y Q) :
    p = Pi.single 0 c := by
  have hc := paid M c
  rw [← bill (K := K) c A ha] at hc
  obtain ⟨_,hp⟩ := Dock.unique_M H.okay hc (fun i _ => EventuallyEq.rfl)
  have hm : letIn h (logMass a) Y = letIn h (logMass a) (archive M c) := by
    unfold letIn
    rw [ArchTurn.archive_h hp (fun i => (Dock.gang (H.okay i)).dost)
      (fun i => (Dock.gang (hc i)).dost)]
  apply (H.unique _ _).symm
  rw [hm,deposited,← basisPrice]
  apply speaks (Y := 0)
  · rw [map_zero,add_zero]
  · exact ⟨Response.zero,Honest.zero⟩

end YM.Integration.WilsonSurveyedColorNamedArchive
end
