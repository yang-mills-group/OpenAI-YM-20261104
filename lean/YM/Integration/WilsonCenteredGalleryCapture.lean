import YM.Integration.WilsonCenteredCompleteSlate
import YM.Integration.WilsonCenteredCompleteFare
import YM.Integration.WilsonCapturedPrimarySoftInventory
import YM.Integration.WilsonCapturedPrimarySoftMount

/-! Complete all-field capture of an arbitrary original occupied Wilson face
and its native finite counterterm, on their one original paid gallery. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredGalleryCapture
open Finset RG Wilson Lattice Marker QuadraticLocal Source Labels Extra.Histories Push.Local Planned.GuardedAtom
open WilsonCenteredFiledAtoms
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

def fare (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ)
    (s : R.Mode) (counter : Finset V) (c : V→ℂ) (Z : Support n) (rad : ℕ) (E κ v μ : ℝ) :=
  WilsonCenteredCompleteGallery.invoice p s w v κ (WilsonCapturedPrimarySoftMount.fare p Z w E rad S Y μ v κ s)
      (WilsonCapturedPrimarySoftInventory.fare p Z w E)+
    ∑j∈counter,WilsonCenteredSingletonFiled.fare p S Y w (R.fire j) (c j) Z rad E κ v μ

theorem original [Countable ι] (A : Gallery X ι o P R) (x : X) (s : R.Mode) (counter : Finset V) (c : V→ℂ)
    (w : V→ℝ) (hw : ∀j,0<w j) {E κ v σ C Λ δ μ : ℝ} (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : A.K.Paid w P.p.B P.p.supportExponent κ) (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (law : P.Lawful σ C Λ δ v) (K : Guard.Keeper P.p P.activities)
    (Z : Support n) (y : Site n) (center : y∈Z)
    (home : ∀j∈s.val,o j∈Z) (hc : ∀j∈counter,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad) (nc : ∀j∈counter,separation (o j) y≤rad)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p S Y w s counter c Z rad E κ v μ)
      (fun U=>(A.density x U).part s-∑j∈counter,c j*(A.density x U).part (R.fire j)) :=by
  have light:=WilsonCapturedPrimarySoftMount.original A.E x s y Z center home rad near w hw regular K law div hv room S Y reader
  let rows:=WilsonCapturedPrimarySoftInventory.fare P.p Z w E (R:=R)
  have published (t : R.Mode) (inside : t.val⊆s.val) : Nonempty (WilsonCenteredSoftInventory.Receipt P Z
      (WilsonCenteredCompleteGallery.soft A x t) (rows t)) :=
    WilsonCapturedPrimarySoftInventory.original A.E x t Z (fun j hj=>home j (inside hj)) w hw regular
  have full:=WilsonCenteredCompleteGallery.original A x S Y Z y s home center K w hw law hv room div hard
    (fun U=>Hard.packet_summing A.K hard P.p.exponent_pos.le hw x U) rows (fun t fit=>(published t fit).some)
    _ light
  exact WilsonCenteredCompleteSlate.original A x s counter c w hw regular hard div hv room P.p.exponent_pos.le law K Z y
    center hc rad nc S Y reader full

end YM.Integration.WilsonCenteredGalleryCapture
