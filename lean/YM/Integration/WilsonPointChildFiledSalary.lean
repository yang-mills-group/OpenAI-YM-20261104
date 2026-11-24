import YM.Integration.WilsonPointChildFiledPress

/-! The filed, inverse-normalized one-child payout consumes the full
    finite-order inverse, including its mixing of strictly lower grades. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiledSalary
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFiledPress WilsonNeutralPointCourse
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {d D:ℕ}

def inverseCost (F:Frame G d)(M:Tilework F)(s:Letter F)(e:ℕ):ℝ:=
  ∑ b:Letter F,∑ t∈Finset.HasAntidiagonal.antidiagonal e, |PowerSeries.coeff t.1 (M b s)|

theorem larch_price (o:Loc G 1)(F:Frame G d)(Y:Plaza F D)(M:Tilework F)(s:Letter F)
    (ν C:ℝ)(p:Studio D)(e r:ℕ)
    (held:∀b:Letter F,∀j≤e,Knoxville (fame _) ν (0,o) (Y b p j r) C):
    Knoxville (fame _) ν (0,o) (larch Y M s p e r) (inverseCost F M s e*C):=by
  classical
  have raw (b:Letter F)(t:ℕ×ℕ)(ht:t∈Finset.HasAntidiagonal.antidiagonal e):= (held b t.2
    (show t.2≤e by have eq:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht;omega)).smul (PowerSeries.coeff t.1 (M b s))
  have wide:=knox_sum (Finset.univ:Finset (Letter F)) (fun b _=>knox_sum (Finset.HasAntidiagonal.antidiagonal e) (raw b))
  simpa only [larch,Kemp.launch,Kemp.surf,Finset.sum_apply,inverseCost,Finset.sum_mul] using wide

theorem reset_at (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (digit:∀j,Site (R.family.S.block j)){N j:ℕ}(live:j<N):
    filed R wood a depth digit N j = larch
      (forward R wood a digit N j (filed R wood a depth digit N (j+1)))
      (transfer R wood a depth digit N j)⁻¹:=by
  unfold filed
  conv_lhs=>rw [show N-j=(N-(j+1))+1 by omega]
  rfl

theorem normalized (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (o:Loc G 1)(digit:∀j,Site (R.family.S.block j)){N j:ℕ}(live:j<N)
    (ν C:ℝ)(s:Letter (R.family.labels.level d))(p:Studio D)(e r:ℕ)
    (paid:∀b:Letter (R.family.labels.level d),∀l≤e,Knoxville (fame _) ν (0,o)
      (forward R wood a digit N j (filed R wood a depth digit N (j+1)) b p l r) C):
    Knoxville (fame _) ν (0,o) (filed R wood a depth digit N j s p e r)
      (inverseCost _ (transfer R wood a depth digit N j)⁻¹ s e*C):=by
  rw [reset_at R wood a depth digit live]
  exact larch_price o _ _ _ _ _ _ _ _ _ paid

end YM.Integration.WilsonPointChildFiledSalary
