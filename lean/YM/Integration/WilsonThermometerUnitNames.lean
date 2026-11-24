import YM.Integration.WilsonThermometerUnchangedGrouping

/-! A bijective change of the physical source label retains every component and native input charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitNames
open Function Filter Finset MeasureTheory Relation Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Ribbons Ribbons.Fibers Ribbons.ManyCopies
open Ribbons.ManyCopies.Muster RG05Readout RG05Readout.Address RG05Readout.Many
open scoped Classical Topology BigOperators
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
local notation "Y" i:max => Stock.census i

theorem license (e:V≃W):License (Y W) (Y V) (e:V→W):=fun _ _=>Finset.mem_powerset.mpr (Finset.subset_univ _)
private theorem allowed (e:V≃W) (i:(Y V).Mode):Lit (Y W) (e:V→W) i.val:=
  ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),e.injective.injOn⟩
def rename (e:V≃W):Poly (Y V)→ₐ[ℂ]Poly (Y W):=feed (fun _=>1) (license e)
def mode (e:V≃W)(i:(Y V).Mode):(Y W).Mode:=(allowed e i).climb

theorem part (e:V≃W) (i:(Y V).Mode) (x:Poly (Y V)):
    (rename e x).part (mode e i)=x.part i:=by
  rw [rename,parts_of_feed,Finset.sum_eq_single i]
  · rw [move,dif_pos (allowed e i)]
    change (Pi.single (mode e i) ((∏a∈i.val,(1:ℂ))*x.part i) : (Y W).Mode→ℂ) (mode e i)=x.part i
    simp
  · intro j _ ne
    have diff:mode e j≠mode e i:=by
      intro same;apply ne;apply Subtype.ext
      exact Finset.image_injective e.injective (congrArg Subtype.val same)
    rw [move,dif_pos (allowed e j)]
    change (Pi.single (mode e j) ((∏a∈j.val,(1:ℂ))*x.part j) : (Y W).Mode→ℂ) (mode e i)=0
    simp [diff.symm]
  · exact fun h=>False.elim (h (Finset.mem_univ _))

variable {G:Gauge}{n:Side}{Q:Rep G n}
def named (V:Type):V≃Unit×V where
  toFun i:=((),i)
  invFun := Prod.snd
  left_inv _:=rfl
  right_inv i:=by rcases i with ⟨⟨⟩,i⟩;rfl

theorem funded (e:V≃W) {rows:V→Three G n} {F:Config G n→Poly (Y V)}
    {o:V→Site n} {w:V→ℝ} {d u σ C β y z:ℝ}
    (real:Q.Lawful σ C β y z)(board:MenuBoard Q rows F o w d u)(live:∀i,0<w i):
    MenuBoard Q (rows ∘ e.symm) (fun U=>rename e (F U)) (o ∘ e.symm) (w ∘ e.symm) d u:=by
  have homes:o=(o ∘ e.symm) ∘ e:=by funext i;simp
  have pocket (i:V):(w ∘ e.symm) (e i)*‖(1:ℂ)‖≤w i:=by simp
  have book:=board.blend (fun _=>(1:ℂ)) (license e) real homes pocket live (fun i=>live (e.symm i))
  have rows' :Many.combine (e:V→W) (fun _=>(1:ℂ)) rows=rows ∘ e.symm:=by
    funext j;unfold Many.combine;rw [Finset.sum_eq_single (e.symm j)]
    · simp
    · intro i _ ne;rw [if_neg (fun h=>ne (e.injective (h.trans (e.apply_symm_apply _).symm))),zero_smul]
    · simp
  rwa [rows'] at book

end YM.Integration.WilsonThermometerUnitNames
end
