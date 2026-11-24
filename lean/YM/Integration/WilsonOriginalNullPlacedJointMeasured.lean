import YM.Integration.WilsonOriginalNullPlacedSchool
import YM.Integration.WilsonOriginalNullPlacedJointGerm
import YM.Integration.WilsonOriginalNullPlacedBlend

/-! Identify the primary actually emitted by the joint signed step with
the measured lower coordinate of any complete original Wilson credit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointMeasured
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedGermMap
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (d N p i:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" j:max => (C₀).path.rep N p j

theorem primary (live:i ≤ N) (home:Opened C₀ d i p) (o:Site ((C₀).side i p))
    (W:Rep G ((C₀).side i p)) (same:W.p=(P₀ i).p) (quiet:∀ U,W.eval U=(P₀ i).eval U)
    (z v w:Coefficient F₀ ((C₀).side i p)) (x:(C₀).label d) {a b c τ:ℝ}
    (zf:z.Format o (C₀).params (P₀ i)) (zp:z.remBound o (P₀ i) τ a)
    (vf:v.Format o (C₀).params W) (vp:v.remBound o W (safety C₀ i) b)
    (vn:projection F₀ (C₀).params W.p.threshold o v=0)
    (wf:w.Format o (C₀).params (P₀ i)) (wp:w.remBound o (P₀ i) (safety C₀ i) c)
    (wn:projection F₀ (C₀).params (P₀ i).p.threshold o w=0)
    (trueField:z.density o S₀ (P₀ i)=v.density o S₀ W+w.density o S₀ (P₀ i)+
      (calValues (C:=C₀) d N p i x ∘ Lattice.translate o)) :
    projection F₀ (C₀).params (P₀ i).p.threshold o z=fitting d N p i R.makes home live x := by
  obtain ⟨Y,yf,named⟩:=WilsonOriginalNullPlacedBlend.column R d N p i home live o x
  have blank:Printed C₀ d N p i o w (w.density o S₀ (P₀ i)):=⟨wf,⟨c,wp⟩,rfl⟩
  obtain ⟨r,land⟩:=WilsonOriginalNullPlacedBlend.joint R d N p i home live o blank yf
  obtain ⟨s,sp⟩:=r.bought
  have whole:z.density o S₀ (P₀ i)=v.density o S₀ W+(beside w Y).density o S₀ (P₀ i):=by
    rw [r.fields,trueField,add_assoc]
  have fit:=WilsonOriginalNullPlacedJointGerm.original C₀ d N p i R.makes live home o W same quiet z v
    (beside w Y) zf zp vf vp r.form sp (congrFun whole)
  rw [vn,zero_add,land,wn,zero_add,named] at fit
  exact fit

theorem selected (live:i<N) (home:Opened C₀ d i p) (y:Site ((C₀).side (i+1) p))
    (W:∀ j,Rep G ((C₀).side j p)) (same:(W i).p=(P₀ i).p) (quiet:∀ U,(W i).eval U=(P₀ i).eval U)
    {ε B D:ℝ} (gate:WilsonOriginalNullPlacedParallel.Joined C₀ d N p i W y ε)
    (h k:Coefficient F₀ ((C₀).side (i+1) p))
    (hf:h.Format y (C₀).params (W (i+1))) (hp:h.remBound y (W (i+1)) (safety C₀ (i+1)) B)
    (hn:projection F₀ (C₀).params (W (i+1)).p.threshold y h=0)
    (kf:k.Format y (C₀).params (P₀ (i+1))) (kp:k.remBound y (P₀ (i+1)) (safety C₀ (i+1)) D)
    (kn:projection F₀ (C₀).params (P₀ (i+1)).p.threshold y k=0)
    (z:Coefficient F₀ ((C₀).side i p)) {κ price:ℝ} :
    let o:=((C₀).path.levels.clock.op i p).ratio.parent y
    let T:=transition (C:=C₀) d N p i (h.density y S₀ (W (i+1))+k.density y S₀ (P₀ (i+1)))
    z.Format o (C₀).params (P₀ i) → z.remBound o (P₀ i) κ price → z.density o S₀ (P₀ i)=T →
    let x:=(fitting d N p i R.makes home live.le).symm (projection F₀ (C₀).params (P₀ i).p.threshold o z)
    ∃ (v w:Coefficient F₀ ((C₀).side i p)) (u e:ℝ),
      v.Format o (C₀).params (W i) ∧ v.remBound o (W i) (safety C₀ i) u ∧
      projection F₀ (C₀).params (W i).p.threshold o v=0 ∧
      w.Format o (C₀).params (P₀ i) ∧ w.remBound o (P₀ i) (safety C₀ i) e ∧
      projection F₀ (C₀).params (P₀ i).p.threshold o w=0 ∧
      u+e ≤ (factor C₀ i)^(-rate)*(B+D) ∧ (factor C₀ i)^rate*mCost C₀ d N p i x ≤ ε*(B+D) ∧
      z.density o S₀ (P₀ i)=v.density o S₀ (W i)+w.density o S₀ (P₀ i)+
        (calValues (C:=C₀) d N p i x ∘ Lattice.translate o) := by
  intro o T zf zp received x
  obtain ⟨v,w,j,u,e,vf,vp,vn,wf,wp,wn,total,fee,step⟩:=gate h k B D hf hp hn kf kp kn
  have chart:=primary R d N p i live.le home o (W i) same quiet z v w j zf zp vf vp vn wf wp wn (received.trans step)
  let φ:=fitting d N p i R.makes home live.le
  have chosen:x=j:=(φ.symm_apply_eq).2 chart
  exact ⟨v,w,u,e,vf,vp,vn,wf,wp,wn,total,chosen ▸ fee,chosen ▸ received.trans step⟩

end YM.Integration.WilsonOriginalNullPlacedJointMeasured
