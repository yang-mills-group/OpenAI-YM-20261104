import YM.Integration.WilsonThermometerWeakMixedFiled

/-! The original gauge door's actual one-block price for a captured physical blade, before the growing-calendar gross bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerClusterProjectionFee
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.alloy.B.a
local notation "J" => (A).clock.J
local notation "L" => R.rolls.L
local notation "β" => (A).clock.hatBeta

def price (m d:ℕ):ℝ:=
  let P:=R.metals.p.profile (J m)
  let target:=R.kit.target (J (m+1)) (J m)
  let scale:=L (J (m+1))
  (Graces.coinFee G P d scale+|2*(scale.val:ℝ)^d *
    (Mercury.volt (β m) P.order P.power * (target.goal scale (β m))⁻¹)|)*Graces.host G P d

private theorem cast_door {m p N d:ℕ} {E:Rep G (R.family.side m p)} {F:Rep G (R.family.side (m+1) p)}
    (D:GaugeDoor F E) (hk:R.family.path.rep N p m=E) (h:R.family.path.rep N p (m+1)=F)
    (u:ℝ) (hp:∀ (o:Site (R.family.side (m+1) p)) (q:Set Wing)(M:Lotus.Leaf F),
      ((A).clock.op m p).ratio.parent o=0 → M.turn∈q → o∈M.crest →
      MergeProof.Along (localSection G d) R.family.path N p m (hol G) o q (duet _ _ _ _ hk h D)
        (Complex.ofReal ∘ M.cicada) (MergeProof.prose M) (entry M) 0 0
        (u*load M) (u*load M) (2*load M)) :
    Address.Plated ((Labels.frames G).level d) R.family.path (localSection G d) (hol G)
      m N p (duet _ _ _ _ hk h D) u:=by
  subst E F
  exact ⟨hp⟩

theorem original (simple:G.Simple) {m N p d:ℕ} (edge:m<N) (dated:d≤J m) :
    Address.Plated (R.family.labels.level d) R.family.path (R.family.localSection d)
      R.family.params m N p (R.doors N p m edge) (price R m d) := by
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  obtain ⟨l,v,Q',T,xv,hq,hZ,hO⟩:=ch.motion N m p edge
  change Address.Plated ((Labels.frames G).level d) R.family.path (localSection G d) (hol G)
    m N p (R.doors N p m edge) (price R m d)
  rw [hO]
  apply cast_door R
  intro o q M h0 hw hc
  exact Graces.RG05_respects simple edge ch.nest R.b.r T xv hq hZ R.b.clock R.b.stamp dated
    o h0 M (price R m d) le_rfl q hw hc

end YM.Integration.WilsonThermometerClusterProjectionFee
end
