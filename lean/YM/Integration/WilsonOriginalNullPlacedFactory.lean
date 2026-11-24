import YM.Integration.WilsonOriginalNullPlacedRough
import YM.Integration.WilsonOriginalNullPlacedFiling

/-! Continue one actually placed, calibrated factory field through its next
physical block. All receipts below are on the same finite Wilson history.
The numerical fee uses the measured incoming mass at this date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedFactory
open Function Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

def wage (i:ℕ) : ℝ :=
  2*((((C₀).S.block i).val:ℝ)^d*|R.y (R.alloy.B.a.clock.J (i+1))|+
    Doors.rate (R.alloy.B.a.S.block i)*stock C₀ (i+1))

theorem received (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, ∀ _:i<N, Opened C₀ d (i+1) p →
      ∀ (y:Site ((C₀).side (i+1) p)) (x:(C₀).label d),
      let lower:=(C₀).path.rep N p i
      let o:=((C₀).path.levels.clock.op i p).ratio.parent y
      let bill:=wage R d i*mCost C₀ d N p (i+1) x
      ∃ z:Coefficient (F₀) ((C₀).side i p), z.Format o (C₀).params lower ∧
        z.remBound o lower (safety C₀ i) bill ∧ (F₀).coeffSize z.x≤bill ∧
        transition (C:=C₀) d N p i ((calValues (C:=C₀) d N p (i+1) x) ∘ Lattice.translate y)=
          z.density o S₀ lower := by
  filter_upwards [WilsonOriginalNullPlacedRough.original R d simple shop] with i paid
  intro N p live home y x lower o bill
  let upper:=(C₀).path.rep N p (i+1)
  let original:=((C₀).factory d N p).entries (i+1) x
  let μ:=mCost C₀ d N p (i+1) x
  let B:=2*stock C₀ (i+1)*μ
  let move:=Tour.placard C₀ R.makes N p live y
  let q:=Drift.stamp y move original
  have stamp:GermGraph.fitting d N p (i+1) R.makes home live x=measuring C₀ d N p (i+1) x:=
    fitting_apply (C:=C₀) d N p (i+1) R.makes home live x
  have genuine:reads (C:=C₀) d N p (i+1) original B:=by
    have cert:=graph_cost d N p (i+1) R.makes home live x
    rw [stamp] at cert;exact cert
  have shape:q.Format y (C₀).params upper:=by simpa only [zero_add] using Drift.stamp_format y move original genuine.1
  have budget:q.remBound y upper (safety C₀ (i+1)) B:=by
    have g:=Drift.stamp_rem y move original genuine.2
    rw [zero_add] at g;exact g
  have head:(F₀).coeffSize q.x ≤ 2*μ:=(size_gap d N p (i+1) R.makes home live x).2
  obtain ⟨z,f,r,h,read⟩:=paid N p live y q B shape budget
  have word:q.density y S₀ upper=(calValues (C:=C₀) d N p (i+1) x) ∘ Lattice.translate y:=by
    have e:=WilsonOriginalNullRelocation.registered C₀ R.makes d N p (i+1) live 0 y original
    rw [zero_add] at e;exact e
  have cost:WilsonOriginalNullPlacedRough.fare R d i ((F₀).coeffSize q.x) B ≤bill:=by
    let L:ℝ:=((C₀).S.block i).val
    let c:=R.y (R.alloy.B.a.clock.J (i+1))
    have l0:0≤L^d:=pow_nonneg (Nat.cast_nonneg _) _
    have base:=mul_le_mul_of_nonneg_left (le_abs_self c) l0
    have left:=mul_le_mul_of_nonneg_right base (Work.G08.size_nonneg (F₀) q.x)
    have right:=mul_le_mul_of_nonneg_left head (mul_nonneg l0 (abs_nonneg c))
    change L^d*c*(F₀).coeffSize q.x+Doors.rate (R.alloy.B.a.S.block i)*B≤
      2*(L^d*(abs c)+Doors.rate (R.alloy.B.a.S.block i)*stock C₀ (i+1))*μ
    calc
      _ ≤ L^d*(abs c)*(2*μ)+Doors.rate (R.alloy.B.a.S.block i)*B := add_le_add (left.trans right) le_rfl
      _ = _ := by dsimp only [B];ring
  refine ⟨z,f,rem_mono r cost,h.trans cost,?_⟩
  rw [←word];exact read

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, ∀ live:i<N, Opened C₀ d (i+1) p → ∀ home:Opened C₀ d i p,
      ∀ (y:Site ((C₀).side (i+1) p)) (x:(C₀).label d),
      let lower:=(C₀).path.rep N p i
      let o:=((C₀).path.levels.clock.op i p).ratio.parent y
      let bill:=wage R d i*mCost C₀ d N p (i+1) x
      ∃ (z v:Coefficient (F₀) ((C₀).side i p)) (a:(C₀).label d),
        z.Format o (C₀).params lower ∧ z.remBound o lower (safety C₀ i) bill ∧
        projection F₀ (C₀).params lower.p.threshold o z=fitting d N p i R.makes home live.le a ∧
        v.Format o (C₀).params lower ∧ v.remBound o lower (safety C₀ i) ((1+4*stock C₀ i)*bill) ∧
        projection F₀ (C₀).params lower.p.threshold o v=0 ∧ mCost C₀ d N p i a≤2*bill ∧
        transition (C:=C₀) d N p i ((calValues (C:=C₀) d N p (i+1) x) ∘ Lattice.translate y)=z.density o S₀ lower ∧
        z.density o S₀ lower=v.density o S₀ lower+(calValues (C:=C₀) d N p i a ∘ Lattice.translate o) := by
  filter_upwards [received R d simple shop] with i run
  intro N p live high home y x lower o bill
  obtain ⟨z,zf,zp,zh,real⟩:=run N p live high y x
  let α:=projection F₀ (C₀).params lower.p.threshold o z
  let a:=(fitting d N p i R.makes home live.le).symm α
  obtain ⟨v,vf,vp,vn,cost,_,pair,shift⟩:=
    WilsonOriginalNullPlacedFiling.original C₀ R.makes d N p i home live.le o z bill zf zp zh
  refine ⟨z,v,a,zf,zp,((fitting d N p i R.makes home live.le).apply_symm_apply α).symm,vf,vp,vn,cost,real,?_⟩
  rw [shift] at pair;exact pair

end YM.Integration.WilsonOriginalNullPlacedFactory
