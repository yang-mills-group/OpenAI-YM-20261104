import YM.OPE.Portfolio.Horizon
import YM.RG05.Strand.Country
/-! # Pin the join of TWO tags at any of the pair's endpoints

 Separates two-tag restoration into prototype (from putting bare singleton
 Cups on one and the **same** rep), and a discrepancy. Not assuming
 disconnected/no flag between Cups, not multiplying normalized values.
 The discrepancy will be propagated from exactly the scale at which it arises,
 without declaring a grouped market on remaining steps. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.RG05.Strand
open Function Filter Lattice RG Wilson Pressure Finset MeasureTheory
open MergeProof Ribbons.ManyCopies Cadet Muster
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Extra.Trajectories MergeProof.Float OPE.Backup
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n:Side}
 {R:Rep G n} {δ θ u:ℝ} {w:V×I→ℝ}{v:V} {T:V→Motion}{A:V→Equiv.Perm V}{q:V→Site n}
 {Y: Config G n→Poly (Names V I)}
local notation "X" => (Names V I)
variable {B:Ward (Names V I)} {o:V×I→Site n}
-- prototype doesn't require mixed feasibility postulated; every mask, and
-- arbitrary positive widths. Do not deduce any singleton costs from just Market.
def base (R:Rep G n)(F:V×I→ Config G n→ℂ)(K:V×I→Res G n) (U:Config G n) : Poly (Names V I) := restore R F K 0 0 U
lemma perennial (X': Type) [Fintype X'] (r:X'→Support n) : Towed w r (fun (_: X') (_: Config G n)=> (0:Poly (Names V I))) R.p.B u 1:=by
    refine ⟨0,Summable.of_finite,fun i=> by simp [SumBudget],fun i=>⟨0,le_rfl,fun U p=>?_,?_⟩⟩
    · rw [Poly.part_nil,norm_zero]; rfl
    unfold wordsPrice; simp
variable (R v q A T o w u) (F:V×I→ Config G n→ℂ)(K:V×I→Res G n)
lemma sends (hp: ∀ i,A i v=i): Serves R F K (base R F K) v T q A o w u 1:=by
    have h r:Borne o r (fun (_:Config G n)=> (0:Poly (Names V I))) R.p.threshold:=⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩
    have hr : rises (0:Poly (Names V I)):= fun i hi=>False.elim (hi rfl)
    refine ⟨0,0, ⟨fun _=> ⟨⟨h _,fun _ hi=>False.elim (hi rfl),fun _=>rfl⟩, fun _=>hr⟩,fun _=> ⟨⟨h _,fun _ hi=>False.elim (hi rfl)⟩, fun _=>hr⟩⟩,?_,?_, ?_, rfl⟩
    · exact perennial (Support n) id
    · exact perennial (Box n) Prod.fst
    exact fun i _=> ⟨hp _,fun U=>⟨fun _ _ _=> (scalar_z _).symm,fun _ _ _=> (scalar_z _).symm⟩⟩
variable {R v q A T o w u F K}
private lemma tune (i: (X).Mode) (hv:i.val.card=2) (k:(X).Mode) (hk:k.val.card < i.val.card) (x:Poly (Names V I)) (h:rises x) : x.part k=0:= by by_contra hw; exact (Nat.not_lt_of_ge (h _ hw)) (hv ▸ hk)
lemma pact (a:(X).Mode)(v':V×I)(hv:v'∈ a.val)(hh:a.val.card=2)(h:Bard R B v T A q o F K Y w R.p.supportExponent)(hL:B.ready a)(hp:R.activities.Valid R.p δ θ)(hw:∀ i,0<w i)(hA:Menu.Arsenal R): ∃ X':Cup R, Blade R (o v') X'.home X'.leaves 0 (4/Poly.toll w a) ∧
        (fun U=>(Y U).part a - (base R F K U).part a)=X'.pays:=by
    obtain ⟨Y', ⟨F',K',hJ,hX,hY,hS,rfl⟩, hg⟩:= h.grants
    have hV:= environs v' a hv hA (fun i=>(hJ.exp i).1) (fun i=>(hJ.flag i).1) hX hY hw
    obtain ⟨k,hk,hK⟩:= Ribbons.socket hV
    let y i U:= bar R.activities (Names V I) U i + Mach X (fun j=> K j i U)
    let z i U:= y i U + K' i U
    let x U:= Mach X (fun j=> F j U)
    let x' U:= x U + ∑ i, F' i U
    let B':= Cup.book R (fun U=> (∑ i,F' i U).part a) k hk
    refine ⟨B',?_,?_⟩
    · rw [← hK] at hV
      exact hV.more (le_of_eq (by ring))
    rw [show _=_ from Cup.booked hp B' _ _ hk rfl]; funext U
    have H': base R F K U=play R X y x U:=by
        unfold base restore play; simp [x,y]
    have he: MarkDiff a (fun U=> (∑ i,F' i U).part a) x' x := by
        intro U; simp only [x', add_sub_cancel_left, and_true]
        intro i hi; rw [Poly.part_sum]; exact sum_eq_zero fun j _=> tune a hh _ hi _ ((hJ.exp j).2 U)
    have hE: ∀ i, MarkDiff a (profile R.activities k i) (z i) (y i) := by
        intro i U; rw [hK]; simp only [z,add_sub_cancel_left,and_true]; exact fun j hh'=> tune a hh j hh' _ ((hJ.flag i).2 U)
    have hz: a≠ (X).quiet:=by rintro H; rw [H] at hh; simp [Census.quiet] at hh
    rw [H', hg U a hL]; exact plays a v' hp (fun U=> Accent.mute ..) (by simp [y,Accent.mute,Accent.bar,Poly.bead]) he hE hz hk U
end YM.RG05.Strand
