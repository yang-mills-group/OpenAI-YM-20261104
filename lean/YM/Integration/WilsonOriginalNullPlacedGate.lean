import YM.Integration.WilsonOriginalNullPlacedReserve
import YM.Integration.WilsonOriginalNullGain

/-! Homogeneous return of a physical canonical null row through any
actual child. The complete new canonical field is retained at its
true parent and charged in that parent's measured currency. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedGate
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {ε:ℝ} (pos:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, i<N → Opened C₀ d (i+1) p → Opened C₀ d i p →
      ∀ (y:Site ((C₀).side (i+1) p)) (q:Coefficient F₀ ((C₀).side (i+1) p)) (B:ℝ),
      let upper:=(C₀).path.rep N p (i+1)
      let lower:=(C₀).path.rep N p i
      let o:=((C₀).path.levels.clock.op i p).ratio.parent y
      q.Format y (C₀).params upper → q.remBound y upper (safety C₀ (i+1)) B →
      projection F₀ (C₀).params upper.p.threshold y q=0 →
      ∃ (v:Coefficient F₀ ((C₀).side i p)) (a:(C₀).label d) (u:ℝ), 0 ≤ u ∧
        v.Format o (C₀).params lower ∧ v.remBound o lower (safety C₀ i) u ∧
        projection F₀ (C₀).params lower.p.threshold o v=0 ∧
        u + mCost C₀ d N p i a ≤ ε*(factor C₀ i)^(-rate)*B ∧
        transition (C:=C₀) d N p i (q.density y S₀ upper)=
          v.density o S₀ lower + (calValues (C:=C₀) d N p i a ∘ Lattice.translate o) := by
  filter_upwards [WilsonOriginalNullPlacedRough.original R d simple shop,
    WilsonOriginalNullPlacedReserve.original R d simple,WilsonOriginalNullGain.stock C₀ pos] with i real tiny reserve
  intro N p live high home y q B upper lower o format fund zero
  have B0:0 ≤ B:=by obtain ⟨a,b,ha,hb,tot,-⟩:=fund;linarith only [ha,hb,tot]
  let ρ:=Doors.rate (R.alloy.B.a.S.block i)
  let bill:=2*ρ*B
  let cols:=stock C₀ i
  have r0:0 ≤ ρ:=(Doors.rate_pos _).le
  have s0:0 ≤ cols:=zero_le_one.trans (stage C₀ i).columns_ge
  have b0:0 ≤ bill:=mul_nonneg (mul_nonneg zero_le_two r0) B0
  obtain ⟨z,zf,zr,zh,push⟩:=real N p live y q B format fund
  have actual:=tiny N p live high y q B format fund zero
  obtain ⟨v,vf,vr,vn,heard,_,pair,field⟩:=
    WilsonOriginalNullPlacedFiling.original C₀ R.makes d N p i home live.le o z bill zf (rem_mono zr actual) (zh.trans actual)
  let α:=projection F₀ (C₀).params lower.p.threshold o z
  let a:=(fitting d N p i R.makes home live.le).symm α
  let u:=(1+4*cols)*bill
  have geometry:(3+4*cols)*2 ≤ 4*(2+4*cols):=by linarith only [s0]
  have cap:4*(2+4*cols)*ρ ≤ ε*(factor C₀ i)^(-rate):=reserve
  have total:u + mCost C₀ d N p i a ≤ ε*(factor C₀ i)^(-rate)*B:=calc
    _ ≤ u+2*bill := add_le_add le_rfl heard
    _ = ((3+4*cols)*2*ρ)*B := by dsimp only [u,bill];ring
    _ ≤ ε*(factor C₀ i)^(-rate)*B := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right geometry r0).trans cap) B0
  refine ⟨v,a,u,mul_nonneg (by linarith only [s0] : 0 ≤ 1+4*cols) b0,vf,vr,vn,total,?_⟩
  rw [field] at pair;exact push.trans pair

end YM.Integration.WilsonOriginalNullPlacedGate
