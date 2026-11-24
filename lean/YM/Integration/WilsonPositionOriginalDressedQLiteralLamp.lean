import YM.Integration.WilsonPositionOriginalDressedQLampColumn
import YM.Push.GRID_APPROXIMATION.Many
import YM.Integration.WilsonMacroscopicForwardTransfer

/-! The actually published near part of the lamp is an original Wilson
cylinder. Its cut is made on its own registered addresses, before either
regulated path or cross reading is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQLiteralLamp
open Lattice Cells RG Wilson Marker QuadraticLocal RG3.Letters
open WilsonRootedKioskOccupiedSlip WilsonPositionOriginalDressedQLampColumn
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]
variable {P:BudgetPoint}{o:V→Site n}{R:Census V}(L:Lamps T I G P o R)
variable (B m:ℕ){w:V→ℝ}{α d:ℝ}

def region (x:Site n):Set (Site n):={z | separation x z ≤ m*(4*B+2)+2*B}
def short (s:R.Mode)(t:T)(U:Config G n):ℂ:=
  portion L s (fun i=>coverNumber B (L.ground i) < m) t U

theorem cylinder [Countable I] (hw:∀v,0<w v)(ha:0 ≤ α)(paid:Gross L w B α d)
    (s:R.Mode)(v:V)(hv:v∈s.val)(t:T):
    Interior (region B m (o v)) (short L B m s t):=by
  classical
  let selected i:=coverNumber B (L.ground i) < m
  have bound:=WilsonPositionOriginalDressedQLampColumn.original (m:=0) L hw ha paid s v hv selected
    (fun _ _ _=>Nat.zero_le _) t
  refine ⟨?_,?_,?_,_,bound⟩
  · intro a U;apply tsum_congr;intro i
    by_cases keep:coverNumber B (L.ground i) < m <;> simp [keep,(L.legal t i).symmetry a U]
  · apply Measurable.tsum;intro i
    by_cases keep:coverNumber B (L.ground i) < m
    · by_cases same:s=L.mode i
      · simpa [keep,Poly.part_send,same] using (L.legal t i).borel
      · simp [keep,Poly.part_send,same]
    · simp [keep]
  · intro U W h;apply tsum_congr;intro i
    by_cases keep:coverNumber B (L.ground i) < m
    · by_cases same:s=L.mode i
      · have iv:o v∈L.ground i:=L.roots i v (same ▸ hv)
        have inside:∀z∈L.ground i,z∈region B m (o v):=by
          intro z hz
          apply (Corona.extent (L.ground i) B iv hz).trans
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ keep.le) _
        have eq: L.nominal t i U=L.nominal t i W:=
          (L.legal t i).sites U W fun e he ht=>h e (inside _ he) (inside _ ht)
        simp [keep,eq]
      · simp [keep,Poly.part_send,same]
    · simp [keep]

theorem tail (hw:∀v,0<w v)(ha:0 ≤ α)(paid:Gross L w B α d)
    (s:R.Mode)(v:V)(hv:v∈s.val)(t:T)(U:Config G n):
    ‖(WilsonRootedKioskOccupiedSlip.bare L t U).part s-short L B m s t U‖ ≤
      (Poly.toll w s*Real.exp (α*m))⁻¹*d:=by
  classical
  let near:Set I:={i|coverNumber B (L.ground i) < m}
  let val(i:I):=(Poly.send (L.mode i) (L.nominal t i U)).part s
  have terms:= (WilsonRootedKioskCompleteFiling.sums L hw ha paid t U).1
  have total:Summable val:=((Poly.get s).hasSum terms.hasSum).summable
  have both:=((total.indicator near).tsum_add (total.indicator nearᶜ))
  have pieces:near.indicator val+nearᶜ.indicator val=val:=by
    ext i
    by_cases h:i∈near <;> simp [Set.indicator,Pi.add_apply,h]
  rw [show (WilsonRootedKioskOccupiedSlip.bare L t U).part s=∑'i,val i from Poly.share terms s]
  rw [show (∑'i,val i)=(∑'i,near.indicator val i)+(∑'i,nearᶜ.indicator val i) from by
    rw [←both];exact congrArg (fun f:I→ℂ=>tsum f) pieces.symm]
  have left:short L B m s t U=(∑'i,near.indicator val i):=by
    apply tsum_congr;intro i
    by_cases h:coverNumber B (L.ground i) < m <;> simp [near,Set.indicator,h,val]
  have right:(∑'i,nearᶜ.indicator val i)=portion L s (fun i=>i∈nearᶜ) t U:=by
    apply tsum_congr;intro i
    by_cases h:i∈nearᶜ <;> simp [h,Set.indicator,val]
  rw [left,add_sub_cancel_left,right]
  exact WilsonPositionOriginalDressedQLampColumn.original L hw ha paid s v hv
    (fun i=>i∈nearᶜ) (fun i h _=>Nat.le_of_not_gt h) t U

end YM.Integration.WilsonPositionOriginalDressedQLiteralLamp
