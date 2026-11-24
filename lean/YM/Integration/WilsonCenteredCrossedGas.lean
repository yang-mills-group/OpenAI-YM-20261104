import YM.Integration.WilsonCenteredActualHardSum
import YM.Integration.WilsonCenteredCapturedHardPrice

/-! The original crossed product of the two regular and hard singleton
readings is the gas of its collected native one-source on every field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCrossedGas
open Finset Function Lattice RG Wilson QuadraticLocal Marker Ac Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCapturePush WilsonCenteredCaptureSlots WilsonCenteredCapturedHardFace
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} {P : Rep G n}
variable (T : ι × ℕ → Support n) (U : Config G n)
abbrev Incidences (ι : Type) := (F : Finset ℕ) × (_ : ↥F) × ι

def unpack (z : Born P T owners U) : Incidences ι :=
  ⟨z.2.val,⟨⟨z.1.2,z.2.property.2.1 (mem_singleton_self _)⟩,z.1.1⟩⟩

theorem distinct : Injective (unpack (P:=P) T U) := by
  rintro ⟨⟨l,i⟩,⟨F,h⟩⟩ ⟨⟨l',i'⟩,⟨F',h'⟩⟩ eq
  have eF:=congrArg Sigma.fst eq
  have ei:=congrArg (fun q : Incidences ι=>q.2.1.val) eq
  have el:=congrArg (fun q : Incidences ι=>q.2.2) eq
  change F=F' at eF
  change i=i' at ei
  change l=l' at el
  cases eF;cases ei;cases el;rfl

theorem inverse (z : Incidences ι) (old : P.activities.admissible P.p U z.1) :
    z ∈ Set.range (unpack (P:=P) T U) := by
  rcases z with ⟨F,⟨⟨i,hi⟩,l⟩⟩
  let z := (l,i)
  have inside : owners z ⊆ F := singleton_subset_iff.mpr hi
  have live : (taken P (T z) (owners z) F).Nonempty := ⟨i, mem_filter.mpr ⟨hi,Or.inl (mem_singleton_self _)⟩⟩
  exact ⟨⟨z,⟨F,old,inside,live⟩⟩,rfl⟩

def each (f : ι × ℕ → Config G n → ℂ) (z : Incidences ι) :=
  if P.activities.admissible P.p U z.1 then
    f (z.2.2,z.2.1.val) U * ∏ j∈z.1.erase z.2.1.val,(P.activities.K j U : ℂ)
  else 0

theorem inGas (K : Guard.Keeper P.p P.activities) (serial : (ι × ℕ) × Finset ℕ ↪ ℕ)
    (f : ι × ℕ → Config G n → ℂ) {a v : ℝ}
    (cost : ForceCost P.p P.activities (entered P K T owners serial f) a) (quiet : P.activities.KBound P.p v) :
    (∑' F,gasMark P.p P.activities U F (entered P K T owners serial f)) =
    ∑' F : Finset ℕ, if P.activities.admissible P.p U F then
      ∑ i∈F,(∑' l,f (l,i) U) * ∏ j∈F.erase i,(P.activities.K j U : ℂ)
      else 0 := by
  have recorded := WilsonCenteredActualHardSum.retained K T owners serial f cost quiet U
  have zeros (s : Incidences ι) (off : s ∉ Set.range (unpack (P:=P) T U)) : each (P:=P) U f s=0 :=
    if_neg (fun h=>off (inverse T U s h))
  have tiled : HasSum (each (P:=P) U f) (∑' F,gasMark P.p P.activities U F (entered P K T owners serial f)) := by
    apply ((distinct T U).hasSum_iff zeros).1
    apply recorded.congr_fun
    intro v
    simp only [comp_apply,each,unpack,if_pos v.2.property.1,owners,sdiff_singleton_eq_erase]
  rw [←tiled.tsum_eq,tiled.summable.tsum_sigma]
  apply tsum_congr
  intro F
  by_cases valid : P.activities.admissible P.p U F
  · rw [(tiled.summable.sigma_factor F).tsum_sigma,tsum_fintype,if_pos valid]
    simp only [each,if_pos valid,tsum_mul_right]
    exact (F.sum_coe_sort (fun i=>(∑' l,f (l,i) U) * ∏ j ∈ F.erase i,(P.activities.K j U : ℂ)))
  · simp [each,valid]

variable {V X μ : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
    (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (w : V → ℝ) (hw : ∀ i,0<w i) {δ κ v : ℝ}
    (regular : D.Paid w P.p.B (P.p.supportExponent+2) δ) (hard : A.K.Paid w P.p.B (P.p.supportExponent+2) κ)
    (quiet : P.activities.KBound P.p v) (left : 0 ≤ v) (room : hitWidth P.p*v ≤ 1)
    (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) (hk : 0 < κ)
    (K : Guard.Keeper P.p P.activities) (serial : (ι × ℕ) × Finset ℕ ↪ ℕ)

include hw regular hard quiet left room za zb hk

theorem original (x : X) (U : Config G n) :
    (∑' F,gasMark P.p P.activities U F (row D A a b Z K serial x)) =
      (D.log x U).part (R.fire a) * (A.gas x U).part (R.fire b) +
        (A.gas x U).part (R.fire a) * (D.log x U).part (R.fire b) := by
  obtain ⟨e,hb,reads⟩:=WilsonCenteredCapturedHardPrice.original D A w hw regular hard quiet left room a b Z za zb hk K serial
  let c := κ⁻¹*(w a*w b)
  have hc : 0<c := mul_pos (inv_pos.mpr hk) (mul_pos (hw _) (hw _))
  let bill := 2*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*δ
  have pc : ForceCost P.p P.activities (row D A a b Z K serial x) (c⁻¹*(bill+(hitWidth P.p*v)*bill)) := by
    refine ⟨fun j=>c⁻¹*e j,?_,fun j=>⟨mul_nonneg (inv_pos.mpr hc).le (reads j).1,fun U=>?_⟩⟩
    · simpa only [BudgetPoint.mass,mul_left_comm (c⁻¹)] using sumBudget_mul_left hb (inv_pos.mpr hc).le
    · exact (le_inv_mul_iff₀ hc).mpr ((reads j).2 x U)
  exact (inGas (query D Z) U K serial (fun z U=>WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2) pc quiet).trans
    (WilsonCenteredCompulsoryCollection.original D A w hw (by linarith [P.p.exponent_pos]) regular hard a b x U).symm

end YM.Integration.WilsonCenteredCrossedGas
