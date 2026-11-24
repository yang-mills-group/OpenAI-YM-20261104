import YM.Integration.WilsonThermometerWeakMixedCapture
import YM.Integration.WilsonThermometerMixedBooked
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorRoster
open Function Filter Finset MeasureTheory Relation Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Ribbons Ribbons.Fibers Ribbons.ManyCopies
open Ribbons.ManyCopies.Muster RG05Readout RG05Readout.Address RG05Readout.Many
open scoped Topology Classical BigOperators
variable {G:Gauge}{n:Side}{I:Type}[Fintype I][DecidableEq I]

def place (i:I):Unit×I:=((),i)

theorem permit:License (Stock.census (Unit×I)) (Stock.census I) place:=fun s _=>mem_univ s

def lift (x:Poly (Stock.census I)):Poly (Stock.census (Unit×I)):=feed (fun _=>1) permit x

theorem words {E:Type}[AddCommGroup E][Module ℂ E](raw:I→E):
    Many.combine place (fun _=>1) raw=raw ∘ Prod.snd:=by
  funext j
  rcases j with ⟨⟨⟩,j⟩
  unfold Many.combine
  rw [sum_eq_single j]
  · simp [place]
  · intro i _ other
    have apart:place i≠((),j):=fun h=>other (congrArg Prod.snd h)
    simp [apart]
  · simp

theorem admit (R:Rep G n){raw:I→Three G n}{F:Config G n → Poly (Stock.census I)}
    {o:I→Site n}{w v:I→ℝ}{d a b c β y z:ℝ}(board:MenuBoard R raw F o w d a)
    (law:R.Lawful b c β y z)(pos:∀i,0<v i)(old:∀i,0<w i)(smaller:∀i,v i≤w i):
    MenuBoard R (raw ∘ Prod.snd) (fun U=>lift (F U)) (o ∘ Prod.snd) (v ∘ Prod.snd) d a:=by
  have live:=(board.blend (q:=o ∘ Prod.snd) (w':=v ∘ Prod.snd) (fun _=>1) permit law rfl
    (fun i=>by simpa only [Function.comp_apply,place,norm_one,mul_one] using smaller i)
    old (fun i=>pos i.2))
  rwa [words] at live

def mask (s:(Stock.census I).Mode):(Stock.census (Unit×I)).Mode:=
  ⟨s.val.image place,mem_univ _⟩

theorem mask_injective:Function.Injective (mask (I:=I)):=by
  intro s t eq
  have h:=congrArg (fun r:(Stock.census (Unit×I)).Mode=>r.val.image Prod.snd) eq
  apply Subtype.ext
  simpa [mask,image_image,Function.comp_def,place] using h

private theorem fits (s:(Stock.census I).Mode):
    Lit (Stock.census (Unit×I)) place s.val:=
  ⟨mem_univ _,fun _ _ _ _ h=>congrArg Prod.snd h⟩

theorem read (x:Poly (Stock.census I))(s:(Stock.census I).Mode):
    (lift x).part (mask s)=x.part s:=by
  classical
  change (∑j,Many.move _ _ place j (((Multi.dilation _ (fun _=>1)) x).part j)).part (mask s)=_
  rw [Poly.part_sum,sum_eq_single s]
  · rw [Many.move,dif_pos (fits s),show (fits s).climb=mask s by rfl,Poly.part_send,Multi.dilation_part]
    simp
  · intro j _ js
    have neq:mask j≠mask s:=fun h=>js (mask_injective h)
    rw [Many.move,dif_pos (fits j),show (fits j).climb=mask j by rfl,Poly.part_send]
    simp [Ne.symm neq]
  · simp

end YM.Integration.WilsonThermometerCorridorRoster
end
