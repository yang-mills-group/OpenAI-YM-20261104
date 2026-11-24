import YM.Integration.WilsonOriginalNullMovedOperator

/-! One original canonical Wilson return at an independently displaced fine
site. The paid relative child goes through the native gauge door. Both
stamps permute the entire original numerical forced list. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedRough
open Function Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical.GermGraph MergeProof Motion
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F" => (C₀).labels.level d
local notation "S" => (C₀).localSection d

def fare (i:ℕ) (a b:ℝ) :=
  (((C₀).S.block i).val:ℝ)^d * (R.y (R.alloy.B.a.clock.J (i+1))) * a + Doors.rate (R.alloy.B.a.S.block i)*b

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, ∀ _:i<N, ∀ (y:Site ((C₀).side (i+1) p))
      (q:Coefficient (F) ((C₀).side (i+1) p)) (B:ℝ),
      let upper:=(C₀).path.rep N p (i+1)
      let lower:=(C₀).path.rep N p i
      let o:=((C₀).path.levels.clock.op i p).ratio.parent y
      let rent:=fare R d i ((F).coeffSize q.x) B
      q.Format y (C₀).params upper → q.remBound y upper (safety (C₀) (i+1)) B →
      ∃ z:Coefficient (F) ((C₀).side i p), z.Format o (C₀).params lower ∧
        z.remBound o lower (safety (C₀) i) rent ∧ (F).coeffSize z.x ≤ rent ∧
        transition (C:=C₀) d N p i (q.density y S upper)=z.density o S lower := by
  filter_upwards [WilsonOriginalNamedRoughRide.original R simple shop d] with i ready
  intro N p live y q B upper lower o rent form bound
  let ratio:=((C₀).path.levels.clock.op i p).ratio
  let t:=ratio.embed o
  let r:=y+-t
  let prev:=Tour.placard C₀ R.makes N p live (-t)
  let q₀:=Drift.stamp (-t) prev q
  have parent:ratio.parent r=0:=by
    change ratio.parent (y+-ratio.embed o)=0
    rw [show -ratio.embed o=ratio.embed (-o) from (ratio.root.map_neg o).symm,
      Next.Rank.Station.parent_offset,show ratio.parent y=o from rfl,add_neg_cancel]
  have qform:q₀.Format r (C₀).params upper:=Drift.stamp_format (-t) prev q form
  have qfund:q₀.remBound r upper (safety (C₀) (i+1)) B:=Drift.stamp_rem (-t) prev q bound
  obtain ⟨z,zform,zfund,zhead,ride⟩:=ready N p live r parent q₀ B qform qfund
  let χ:ℂ:=((C₀).S.block i).val
  have pos:χ≠0:=Nat.cast_ne_zero.mpr ((C₀).S.block i).pos.ne'
  have step₀:transition (C:=C₀) d N p i (q₀.density r S upper)=z.density 0 S lower:=by
    have eq:=ride.exactStep
    change (χ^d)⁻¹ • z.density 0 S lower=(1:ℂ) • ((C₀).path.levels.clock.op i p).push upper.beta (q₀.density r S upper) at eq
    rw [one_smul] at eq
    have h:=congrArg (fun f:Config G ((C₀).side i p)→ℂ=>(χ^d)•f) eq
    change (χ^d) • ((χ^d)⁻¹ • z.density 0 S lower)=_ at h
    rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero d pos),one_smul] at h
    exact h.symm
  let move:=Tour.placard C₀ R.makes N p live.le o
  refine ⟨Drift.stamp o move z,?_,?_,zhead,?_⟩
  · simpa only [zero_add] using Drift.stamp_format o move z zform
  · have fee:z.remBound 0 lower (safety C₀ i) rent:=zfund
    have shifted:=Drift.stamp_rem o move z fee
    rw [zero_add] at shifted
    exact shifted
  · have undo:q₀.density r S upper=(q.density y S upper) ∘ Lattice.translate (-t):=
      WilsonOriginalNullRelocation.registered C₀ R.makes d N p (i+1) live y (-t) q
    have hi:Integrable (q₀.density r S upper) (prior G _):=
      (q₀.envelope S (R.makes.wilson.represents N p (i+1) live).good qfund qform).integrableC (prior G _)
    have rest:(Drift.stamp o move z).density o S lower=(z.density 0 S lower) ∘ Lattice.translate o:=by
      simpa only [zero_add,Function.comp_def] using WilsonOriginalNullRelocation.registered C₀ R.makes d N p i live.le 0 o z
    have raw:(q₀.density r S upper) ∘ Lattice.translate t=q.density y S upper:=by
      rw [undo,WilsonOriginalNullMovedOperator.undo]
    calc
      _ = transition (C:=C₀) d N p i ((q₀.density r S upper) ∘ Lattice.translate t):=congrArg _ raw.symm
      _ = (transition (C:=C₀) d N p i (q₀.density r S upper)) ∘ Lattice.translate o:=
        WilsonOriginalNullMovedOperator.commute C₀ d N p i o _ hi
      _ = _ := (congrArg (fun f:Config G ((C₀).side i p)→ℂ=>f ∘ Lattice.translate o) step₀).trans rest.symm

end YM.Integration.WilsonOriginalNullPlacedRough
