import YM.Integration.WilsonThermometerOffsetLedger

/-! The two original RG05 charges for a placed coefficient are bounded on the
very step on which the native address is purchased. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyStageFare
open Filter Set Lattice RG Wilson Source Labels PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open YM.UVExtension UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Bid Planned.GuardedAtom Guard Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bandage
open WilsonLimitConstruction RG05Readout RG05Readout.Address
open scoped Classical Topology

open RG05Readout.Copper RG05Readout.Native
variable {G : Gauge} (R : Run G) (hG : G.Simple)

open RG05Readout.UV




private theorem bound {d j:ℕ}{L:Side}{P:Stage}{c K B B' Q β:ℝ}
    (paid:Crossed d j L P c K B B' Q β) (cost:1≤c) (ko:1≤K)
    (bo:0≤β) (ro:0≤B) : c≤(L.val:ℝ) ∧ β≤(L.val:ℝ):=by
  have kp:0≤K:=zero_le_one.trans ko
  have cp:0≤c:=zero_le_one.trans cost
  have ac:1≤aCost d K:=ko.trans (le_add_of_nonneg_right (by positivity))
  have ac0:=zero_le_one.trans ac
  have ap:0≤1+c+β+K*c:=by positivity
  have fee:1+c+β+K*c≤tollP d K c β:=by
    exact le_mul_of_one_le_left ap ac
  have slip:0≤tollV d L K c (Doors.rate L) β:=by
    have hp:0≤Doors.rate L:=(Doors.rate_pos _).le
    dsimp only [tollV]
    positivity
  have turn:0≤roughT P:=by unfold roughT Push.Local.turnCost;positivity
  have tk:0≤tollV d L K c (Doors.rate L) β * roughT P * B:=by positivity
  have side:1≤(L.val:ℝ):=by exact_mod_cast L.property
  have smaller:lamp L j≤(L.val:ℝ):=Real.rpow_le_self_of_one_le side
    ((div_le_one₀ (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) j]))
  have z:=paid.tickets.trans smaller
  constructor <;> nlinarith only [fee,tk,z,ap,mul_nonneg kp cp,cp,bo]

include hG in
/-- Both costs are the literal ones in the measured address and held Ride. -/
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop, 1≤R.y (R.alloy.B.a.clock.J (m+1)) ∧
      R.y (R.alloy.B.a.clock.J (m+1))≤((R.family.S.block m).val:ℝ) ∧
      0≤RG05Readout.Copper.swing G (R.alloy.B.a.params (m+1)) ∧
      RG05Readout.Copper.swing G (R.alloy.B.a.params (m+1))≤((R.family.S.block m).val:ℝ):=by
  let A:=R.alloy.B.a
  filter_upwards [A.fits.deep.eventually_ge_atTop (d+3)] with m grade
  have hit:Push.Local.hitWidth (R.family.path.rep (m+1) 0 m).p*Push.Local.kappa R.family.path m≤1:=
    (R.makes.wilson.represents (m+1) 0 m (Nat.le_succ m)).vac.symm ▸ UV.stalls R.b m
  have fine:Push.Local.kappa R.family.path (m+1)≤1:=
    (le_mul_of_one_le_left (Real.sqrt_nonneg _) (Push.Local.width_one_le (A.budget (m+1)))).trans (UV.stalls R.b (m+1))
  obtain ⟨T,plot⟩:=WilsonCloseCaptureAddress.issued R hG shop d m (m+1) 0 (Nat.lt_succ_self m) grade hit fine
  let i:=A.clock.J (m+1)
  let j:=A.clock.J m
  have H:=shop.crossed i j d (step_paid A m).1 ((Nat.le_add_right d 3).trans grade)
  have kp:= (k_found G (R.metals.p.profile j) d).choose_spec.1
  have rp:=zero_le_one.trans (cash_fill G d i R.metals.p.profile R.y).choose_spec.1
  have ep:RG05Readout.Copper.swing G (R.metals.p.profile i)=RG05Readout.Copper.swing G (A.params (m+1)):=by rw [Push.PriceCompiler.params_eq R.alloy.B.valid (m+1)]
  have bz:=ep.ge.trans' plot.b_pos
  have both:=bound H plot.posp kp bz rp
  rw [ep,← Push.PriceCompiler.block_eq R.alloy.B.valid m] at both
  exact ⟨plot.posp,both.1,plot.b_pos,both.2⟩

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyStageFare
