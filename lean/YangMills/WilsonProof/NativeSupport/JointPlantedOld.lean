import YangMills.WilsonProof.NativeSupport.JointPlantLedger
import YangMills.WilsonProof.NativeSupport.JointMountedBill

/-! Identify the coefficients of the recolored physical intake that have
no current births. Its old-price bill is that of the previous original
sheet. Every vivid input has an eligible owner. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker Extra.Trajectories MergeProof MergeProof.Accent MergeProof.Menu RGGapR2 Packet Painted
open scoped Classical BigOperators
variable {V J:Type} [Fintype V] [DecidableEq V] [Fintype J] {G:Gauge} {n:Side}
local notation "B" => Stock.census V
local notation "C" => Stock.census (Ink V)
variable (R:Rep G n) (o:V → Site n) (H:Support n → Config G n → Marker.Poly (Stock.census V)) (K:Box n → Config G n → Marker.Poly (Stock.census V))
variable (birth:J → V) (X:J → Support n) (v:J → Config G n → ℂ) (born:Finset V) (hb:∀ j,birth j∈born)

def liftSheet {I:Type} (f:I → Config G n → Marker.Poly (Stock.census V)) (i:I) (Z:Config G n) := repaint (f i Z)
local notation "a₀" => (fun j:J=>newborn (birth j))
local notation "H₀" => liftSheet H
local notation "K₀" => liftSheet K
local notation "E" => plantedLog R C H₀ a₀ X v
local notation "D" => plantedDirty R C K₀ a₀ X v
local notation "M" => (Stock.census (Ink V)).Mode

theorem lift_ledger (ledger:Rough.Ledger o H K R.p.threshold) : Rough.Ledger (o ∘ Prod.fst) H₀ K₀ R.p.threshold := by
  refine ⟨fun i=>⟨born_repaint _ (ledger.exp i).toBorne,?_,?_⟩,fun i=>⟨⟨born_repaint _ (ledger.flag i).1.toBorne,?_⟩,?_⟩⟩
  · exact fun Z live=>(ledger.exp i).permits Z (fun eq=>live (by rw [liftSheet,eq,repaint_nil]))
  · exact fun Z=>(repaint_quiet _).trans ((ledger.exp i).sil Z)
  · exact fun Z live=>(ledger.flag i).1.permits Z (fun eq=>live (by rw [liftSheet,eq,repaint_nil]))
  · exact fun Z=>(repaint_quiet _).trans ((ledger.flag i).2 Z)

include hb in
theorem planted_old_parts (ledger:Rough.Ledger o H K R.p.threshold) {a quiet:ℝ} (vac:R.activities.Valid R.p a quiet) (p:M) (nz:p ≠ (Stock.census (Ink V)).quiet)
    (none:Disjoint (p.val.image Prod.fst) born) :
    (∀ i Z,(E i Z).part p=(H₀ i Z).part p) ∧ (∀ i Z,(D i Z).part p=(K₀ i Z).part p) := by
  let freshSet:=univ.filter (fun z:Ink V=>z.1∈born)
  have ds:Disjoint p.val freshSet := disjoint_left.mpr fun i hi mem=>
    disjoint_left.mp none (mem_image_of_mem _ hi) (mem_filter.mp mem).2
  have births (j:J): a₀ j∈freshSet := mem_filter.mpr ⟨mem_univ _,hb j⟩
  have unhit (j:J):p ≠ (Stock.census (Ink V)).fire (a₀ j) := by
    intro eq
    exact disjoint_left.mp ds (eq ▸ mem_singleton_self _) (births j)
  have noFresh (j:J) (Z:Config G n) : (fresh R C a₀ X v true j Z).part p=0 := by
    rw [fresh,Poly.part_send,if_neg (unhit j)]
  constructor
  · intro i Z
    change (H₀ i Z+tally X (fresh R C a₀ X v true) i Z).part p=_
    rw [Poly.part_plus,tally,Poly.share (Summable.of_finite : Summable (fun k:{j:J // X j=i}=> fresh R C a₀ X v true k.val Z))]
    rw [show (∑' k:{j:J // X j=i},(fresh R C a₀ X v true k.val Z).part p)=0 from
      (tsum_congr fun (k:{j:J // X j=i})=>noFresh k.val Z).trans tsum_zero,add_zero]
  · intro i Z
    let gas:=exclaim R.activities C+K₀
    have laws (j:Box n) (hit:gas j Z ≠ 0) : j.1∩flags R.p.threshold Z=j.2 ∧ Sure j := by
      by_cases blank:exclaim R.activities C j Z=0
      · apply ((lift_ledger R o H K ledger).flag j).1.permits Z
        intro missing
        exact hit (by change exclaim R.activities C j Z+liftSheet K j Z=0; rw [blank,missing,zero_add])
      · exact (granular R.activities R.p C (o:=o ∘ Prod.fst) vac j).permits Z blank
    let h j Z:=if Healthy R.p.threshold (X j) Z ↔ false=true then v j Z else 0
    have unchanged:=old_closure gas X R.p.threshold Z i a₀ freshSet births h p.val ds laws
    change (if p=(Stock.census (Ink V)).quiet then 0 else (plantedFull R C K₀ a₀ X v i Z).part p)=_
    rw [if_neg nz]
    have remaining : (gas i Z).part p=(K₀ i Z).part p := by
      change (exclaim R.activities C i Z+K₀ i Z).part p=_
      rw [Poly.part_plus]
      change (Poly.send (Stock.census (Ink V)).quiet _).part p+_=_
      rw [Poly.part_send,if_neg nz,zero_add]
    exact unchanged.trans remaining

theorem old_envelope {X':Type} (F:X' → Config G n → Marker.Poly (Stock.census V)) (A:X' → Config G n → Marker.Poly (Stock.census (Ink V)))
    (cap:X' → Finset V → ℝ) (value:∀ i U s,‖(F i U).part (tag s)‖ ≤ cap i s)
    (proper:∀ i U,(A i U).part (Stock.census (Ink V)).quiet=0) (nn:∀ i s,0 ≤ cap i s)
    (retain:∀ (p:M),p ≠ (Stock.census (Ink V)).quiet → Disjoint (p.val.image Prod.fst) born →
      ∀ i Z,(A i Z).part p=(repaint (F i Z)).part p) :
    (∀ i Z (p:M),¬gains born p.val → ‖(A i Z).part p‖ ≤ oldCap (cap i) p) ∧
    (∀ i (p:M),Vivid A i p → ∃ a∈p.val,a∈active born) := by
  constructor
  · intro i Z p low
    by_cases equal:p=(Stock.census (Ink V)).quiet
    · rw [equal,proper,norm_zero]
      unfold oldCap
      split; exact nn ..; rfl
    rw [retain p equal (old_or_gain born p.val low).1 i Z]
    change ‖(repaint (F i Z)).part (tag p.val)‖ ≤ _
    rw [repaint_part]
    unfold oldCap
    split
    · exact value .. 
    · exact (norm_zero : ‖(0:ℂ)‖=0).le
  · intro i p live
    obtain ⟨Z,valueZ⟩:=live
    have properP:p ≠ (Stock.census (Ink V)).quiet := fun eq=>valueZ (eq ▸ proper i Z)
    by_cases bornHit:∃ a∈p.val,a.1∈born
    · obtain ⟨u,hu,yes⟩:=bornHit
      exact ⟨u,hu,mem_filter.mpr ⟨mem_univ _,Or.inr yes⟩⟩
    have noBirth:Disjoint (p.val.image Prod.fst) born := by
      apply disjoint_left.mpr
      intro a ha mem
      obtain ⟨u,hu,rfl⟩:=mem_image.mp ha
      exact bornHit ⟨u,hu,mem⟩
    rw [retain p properP noBirth i Z] at valueZ
    change (repaint (F i Z)).part (tag p.val) ≠ 0 at valueZ
    rw [repaint_part] at valueZ
    split at valueZ
    next wore =>
      have nonempty : (p.val.image Prod.fst).Nonempty := by
        obtain ⟨u,hu⟩:=nonempty_iff_ne_empty.mpr (fun eq=>properP (Subtype.ext eq))
        exact ⟨u.1,mem_image_of_mem _ hu⟩
      obtain ⟨u,hu,yes⟩:=old_owns born _ nonempty
      exact ⟨u,wore ▸ hu,yes⟩
    next => contradiction

end YM.Integration.InletSusceptibility.JointShadow
