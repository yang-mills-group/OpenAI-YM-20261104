import YM.Integration.WilsonThermometerWeakMixedGrouping
import YM.Integration.WilsonCloseCaptureFinances

/-! On the original funded course use the physical clustering purchase attached to the same regular and forced merger. The two Boolean filings can be grouped at the ordinary three-slot test weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedCapture
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Ribbons
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open MergeProof.Float MergeProof.Ribbon Pressure
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonMixedTaggedPrice
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem combined {E:Type*} [AddCommGroup E] [Module ℂ E] (z:ℂ) (f:I→E) :
    Many.combine Prod.fst (WilsonMixedTaggedPrice.weight Prod.snd z) (liveRow f)=f := by
  funext j
  unfold Many.combine
  rw [Finset.sum_eq_single (j,false)]
  · simp [WilsonMixedTaggedPrice.weight,liveRow]
  · rintro ⟨k,t⟩ _ ne
    cases t with
    | false=>
      have different : k≠j:=fun he=>ne (by rw [he])
      simp [different]
    | true=>simp [liveRow]
  · simp

theorem filed {P:Rep G n} {α β b y E t:ℝ} {F:Config G n→Poly (census (Stock.census I))}
    {raw:I→Three G n} {o:I→Site n} {w:I→ℝ} (hr:P.Lawful α β b y E)
    (board:MenuBoard P (liveRow raw) F (o ∘ Prod.fst) (w ∘ Prod.fst) t 1)
    (hw:∀i,0<w i) {z:ℂ} (hz:‖z‖≤1) :
    MenuBoard P raw (fun U=>specialize (Stock.census I) z (F U)) o w t 1 := by
  have hV (v:I×Bool): w v.1*‖WilsonMixedTaggedPrice.weight Prod.snd z v‖ ≤ w v.1 := by
    apply mul_le_of_le_one_right (hw _).le
    rcases v with ⟨i,b⟩
    cases b <;> simp [WilsonMixedTaggedPrice.weight,hz]
  have qr:=board.blend (WilsonMixedTaggedPrice.weight Prod.snd z) (WilsonMixedTaggedRoster.project (Stock.census I)) hr rfl hV
    (fun i=>hw i.1) hw
  rwa [combined] at qr

variable (R:Run G) {N per:ℕ}
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "P" m => R.family.path.rep N per m

theorem original (cater:Cater R.family R.doors) {j:ℕ} (edge:j+1<N)
    (L:Fibers I J) (H l:ℕ) (order:0<H) (enough:∀v,(L.contents v).card ≤ H)
    (raw:I→Three G (R.family.side (j+2) per)) (down:I→Three G (R.family.side (j+1) per))
    (o:I→Site (R.family.side (j+2) per)) (w cost:I→ℝ)
    (F:Config G (R.family.side (j+2) per)→Poly (census (Stock.census I)))
    (board:MenuBoard (P (j+2)) (liveRow raw) F (o ∘ Prod.fst) (w ∘ Prod.fst)
      (((A).budget (j+2)).supportExponent-1) 1)
    (hw:∀i,0<w i) (ride:∀i,Ride ((A).clock.op (j+1) per) (o i)
      (((A).clock.op (j+1) per).ratio.parent (o i)) (R.doors N per (j+1) edge) 1 (raw i) (down i) (cost i))
    (upper:Occupancy o (apron (A) (j+1)))
    (lower:Occupancy (((A).clock.op (j+1) per).ratio.parent ∘ o) (apron (A) (j+1)))
    (cash:∀i,2*w i*cost i≤1)
    (close:∀ i,coverNumber (P (j+1)).p.B
      ({((A).clock.op (j+1) per).ratio.parent (o (L.twig (L.bunch i))),((A).clock.op (j+1) per).ratio.parent (o i)}:
          Support (R.family.side (j+1) per)) ≤ l) :
    ∀ z:ℂ,‖z‖≤1 →
      let X:=((A).clock.op (j+1) per).push (P (j+2)).beta (fun U=>specialize (Stock.census I) z (F U))
      let placements:=((A).clock.op (j+1) per).ratio.parent ∘ o ∘ L.twig
      let fees:=WilsonThermometerWeakMixedGrouping.radius L (P (j+1)) H l (renal (A) (j+1))
        (fun i=>renal (A) (j+1)*w i)
      ∃ g:J → Config G (R.family.side (j+1) per)→ℂ,∃ K:J→ℕ → Config G (R.family.side (j+1) per)→ℂ,
        Served (P (j+1)) g (fun v=>profile (P (j+1)).activities (K v)) (fun U=>Fibers.reap L (X U))
          placements fees (P (j+1)).p.supportExponent 1 ∧
        ∀ v,Dominated (K v) ∧ Blade (P (j+1)) (placements v) (g v) (profile (P (j+1)).activities (K v))
          0 (4*(1/fees v)) := by
  obtain ⟨a,t,course,bars⟩:=cater.tiers (j+1) N per edge
  obtain ⟨a',t',prev,_⟩:=cater.tiers j N per (show j<N by omega)
  have physical:=R.makes.wilson
  have good:=physical.represents N per (j+1) edge.le
  intro z hz
  have fine:=filed (physical.represents N per (j+2) edge).good board hw hz
  have next:=course.plates physical edge fine (by linarith) (ν:=fun _=>1)
    (fun _=>by simp) hw ride upper lower cash
  simp only [inv_one,one_smul] at next
  have fee:=bars
  unfold Ribbons.scurry at fee
  have he:(P (j+1)).p=(A).budget (j+1):=good.vac
  rw [←he] at fee
  exact WilsonThermometerWeakMixedGrouping.grouped L _ next prev.publishes.contact good.good.labels
    (fun U=>(Tour.bright R.family.path physical N per _ edge.le U).ne')
    (fun i=>mul_pos course.poses.hats.1 (hw i)) lower order enough close
    course.poses.hats.1 course.poses.hats.2 fee

end YM.Integration.WilsonThermometerWeakMixedCapture
end
