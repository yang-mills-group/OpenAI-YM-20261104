import YM.Integration.WilsonCloseCaptureAddress

/-! The complete presold signed ultraviolet price on the already selected trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCaptureSignedPrice
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
include hG

theorem purchased (shop : RG05Preconstruction.ReadoutPurchase R.b) : UV.Lacquer R.family R.doors := by
  let A := R.alloy.B.a
  let C := R.family
  let V := R.metals.p.profile
  let pay (d i : ℕ) := ash G d (A.clock.J i) V R.y
  have profile (i : ℕ) : A.params i = V (A.clock.J i) := params_eq R.alloy.B.valid i
  refine ⟨pay,fun d m => (show C.path.levels.params m = _ from profile m) ▸
    (cash_fill G d (A.clock.J m) V R.y).choose_spec.2.1,fun d => ?_⟩
  filter_upwards [A.fits.deep.eventually_ge_atTop (d+3),wraps C hG d] with m level wrap p N live
  have fpos : 0 ≤ Push.Local.kappa C.path (m+1) := Real.sqrt_nonneg _
  have coarse : Push.Local.hitWidth (C.path.rep N p m).p*Push.Local.kappa C.path m ≤ 1 :=
    (R.makes.wilson.represents N p m live.le).vac.symm ▸ UV.stalls R.b m
  have fine : Push.Local.kappa C.path (m+1) ≤ 1 :=
    (le_mul_of_one_le_left fpos (Push.Local.width_one_le (A.budget (m+1)))).trans (UV.stalls R.b (m+1))
  obtain ⟨T,hT⟩ := WilsonCloseCaptureAddress.issued R hG shop d m N p live level coarse fine
  let i := A.clock.J (m+1)
  let j := A.clock.J m
  let stage := V j
  have same : A.params m=stage := profile m
  let Q := inverseFuel G d (R.y i) stage
  apply enamel R.makes live hT (Q:=Q)
  · change Crossed d i (A.S.block m) (A.params (m+1)) (R.y i) (optics G (A.params m) d) (pay d (m+1)) (pay d m) Q (swing G (A.params (m+1)))
    rw [profile,same,show A.S.block m= R.rolls.L i from Push.PriceCompiler.block_eq R.alloy.B.valid m]
    exact shop.crossed i j d (step_paid A m).1 ((Nat.le_add_right d 3).trans level)
  · exact zero_le_one.trans (le_max_left ..)
  · unfold Q; rw [same]; exact le_max_right ..
  · rw [same]; exact (cash_fill G d j V R.y).choose_spec.2.2 i (A.fits.stepSlow m)
  · exact (cash_fill G d i V R.y).choose_spec.1
  · exact (cash_fill G d j V R.y).choose_spec.1
  · rw [(R.makes.wilson.represents N p m live.le).vac,(R.makes.wilson.represents N p (m+1) live).vac]
    exact max_le (wrap p).1 (wrap p).2

end YM.Integration.WilsonCloseCaptureSignedPrice
