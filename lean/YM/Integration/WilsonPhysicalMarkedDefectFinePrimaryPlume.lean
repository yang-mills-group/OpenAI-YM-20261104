import YM.WilsonCoeffUV.Marked.Paths.PostRank

/-! The original localSection stencil has finite true support. Periodizing its
infinite-volume upper WUV herald is therefore exactly the torus upper herald,
including all winding collisions on small tori. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.FinePrimary
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08 Wilson Tree PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Power
open Precision Exterior Source Source.Drops Labels Next.Foundations
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem finite_images {ι P V:Type} [Fintype ι] [DecidableEq P] [NormedAddCommGroup V] {r:ℕ}
    (X:ι→dock Cover P r) (w:ι→V) (n:Side) (t:dock (Site n) P r):
    Carp.plume (fun z=>∑a,if X a=z then w a else 0) n t=∑a,if slideC n (X a)=t then w a else 0:=by
  let val:=fun a=>if slideC n (X a)=t then w a else 0
  have one (a:ι):HasSum (fun z=>if X a=z then val a else 0) (val a):=by
    simpa only [eq_comm] using hasSum_ite_eq (X a) (val a)
  have sum:=hasSum_sum (s:=Finset.univ) (fun a _=>one a)
  unfold Carp.plume
  apply HasSum.tsum_eq
  apply sum.congr_fun
  intro z
  unfold Carp.peglet
  by_cases hz:slideC n z=t
  · rw [if_pos hz];apply Finset.sum_congr rfl
    intro a _;by_cases ha:X a=z <;> simp [ha,val,hz]
  · rw [if_neg hz];symm;apply Finset.sum_eq_zero
    intro a _;by_cases ha:X a=z <;> simp [ha,val,hz]

theorem local_fold {h D:ℕ} {F:Frame G h} (T:SectionData F) (w:h<D) (v:Alma F) (n:Side) (e r:ℕ):
    Carp.plume (anthem T w v e r) n=herald T w v n e r:=by
  let f:=sprig (collar T (sheet F v)) (valence F v) e
  let Q:=jewelBloom w v
  let x:=dance T
  have ht:anthem T w v e r=fun y=>fade (spear x) f r y • Q:=by
    by_cases hv:valence F v+e=r
    · subst r;rw [anthem,shine_lit];rfl
    · ext1 y;rw [anthem,shine_dark hv];unfold fade f sprig;simp only [shine_dark hv,Pi.zero_apply];simp
  have collect {U:Type} (g:Toe T→U) (z:Fin r→U)[DecidableEq U]:
      fade (spear g) f r z • Q=∑a:Fin r→Toe T,if g ∘ a=z then f r a • Q else 0:=by
    rw [fade,Finset.sum_smul];apply Finset.sum_congr rfl;intro a _
    split
    next yes=>rw [←yes];simp [spear]
    next no=>obtain ⟨i,hi⟩:=Function.ne_iff.mp no
             rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul,zero_smul]
             rw [spear,Matrix.of_apply,if_neg];exact hi.symm
  have real:anthem T w v e r=fun y=>∑a:Fin r→Toe T,if x ∘ a=y then f r a • Q else 0:=by
    rw [ht];funext y;exact collect x y
  rw [real]
  funext z
  change Carp.plume _ n z=fade (spear (foldUnder n ∘ x)) f r z • Q
  rw [collect,finite_images (fun a:Fin r→Toe T=>x ∘ a) (fun a=>f r a • Q)]
  rfl

end YM.Integration.WilsonPhysicalMarkedDefect.FinePrimary
end
