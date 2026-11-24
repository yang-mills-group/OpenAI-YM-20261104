import YM.Integration.WilsonCloseCaptureSignedPrice
import YM.RG05Readout.Address.Lit

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedRoughRide
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
variable {G : Gauge} (R : Run G) (hG : G.Simple)

local notation "C" => R.family
local notation "A" => R.alloy.B.a
open Push.Local

include hG
/-- A genuine incoming coefficient on the canonical Wilson representation, with
its complete forced array, buys one ordinary-insertion Ride on the same door. -/
theorem original (purchase:RG05Preconstruction.ReadoutPurchase R.b) (d:ℕ) :
    ∀ᶠ j:ℕ in atTop, ∀ N p (edge:j<N) (o:Site ((C).side (j+1) p)),
      ((C).path.levels.clock.op j p).ratio.parent o=0 →
      ∀ (q:Coefficient ((C).labels.level d) ((C).side (j+1) p)) (B:ℝ),
      let upper:=(C).path.rep N p (j+1)
      let lower:=(C).path.rep N p j
      let L:ℝ:=((C).S.block j).val
      let χ:ℂ:=((C).S.block j).val
      let c:=R.y ((A).clock.J (j+1))
      let α:=Doors.rate ((A).S.block j)
      let β:=2*(Real.exp upper.p.supportExponent*Cub.title G ((A).params (j+1)))
      let W:=((C).labels.level d).coeffSize q.x
      let u:=L^d*c
      q.Format o (C).params upper → q.remBound o upper (kappa (C).path (j+1)) B →
      ∃ z:Coefficient ((C).labels.level d) ((C).side j p),
        z.Format 0 (C).params lower ∧ z.remBound 0 lower (kappa (C).path j) (u*W+α*B) ∧
        ((C).labels.level d).coeffSize z.x ≤ u*W+α*B ∧
        Ride ((C).path.levels.clock.op j p) o 0 (R.doors N p j edge) 1
          (invoice q o ((C).localSection d) upper)
          ((χ^d)⁻¹ • invoice z 0 ((C).localSection d) lower)
          ((1+u+β)*W+(2+α)*B) := by
  filter_upwards [(A).fits.deep.eventually_ge_atTop (d+3)] with j eligible
  intro N p edge o parent q B upper lower L χ c α β W u fmt bill
  obtain ⟨T,a,book,afford⟩:=WilsonCloseCapturePositions.positions R hG purchase d N j p edge eligible
  have hc:1≤c:=book.lower.price.trans ((triangle_cost1 _ book.lower.price).trans afford)
  have hp:0≤α:=(Doors.rate_pos _).le
  have hβ:0≤β:=mul_nonneg zero_le_two
    (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Next.Foundations.price_one_le ..)))
  have hκ:kappa (C).path (j+1)≤1:=(le_mul_of_one_le_left (Real.sqrt_nonneg _)
    (width_one_le ((A).budget (j+1)))).trans (UV.stalls R.b (j+1))
  obtain ⟨z,hz,pay,ride,size⟩:=Address.rough C N j p d o _ R.makes edge parent book hp q hc hβ hκ fmt bill
  refine ⟨z,hz,pay,size,?_⟩
  have one:1≤L:=by
    change 1≤(((C).S.block j).val:ℝ)
    exact_mod_cast (show 1≤((C).S.block j).val from ((C).S.block j).pos)
  have cn:χ^d≠0:=pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((C).S.block j).pos))
  have cc:‖(χ^d)⁻¹‖≤1:=by
    rw [norm_inv,norm_pow]
    change (((‖(((C).S.block j).val:ℂ)‖)^d))⁻¹≤1
    rw [Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ one)
  change Ride ((C).path.levels.clock.op j p) o 0 (R.doors N p j edge) (χ^d)
    (invoice q o ((C).localSection d) upper) (invoice z 0 ((C).localSection d) lower)
    ((1+u+β)*W+(2+α)*B) at ride
  have lifted:=ride.matchPay (1:ℂ) ((χ^d)⁻¹) 1 (by rw [inv_mul_cancel₀ cn,one_mul])
  simpa only [one_smul,norm_one,max_eq_left cc,one_mul] using lifted

end YM.Integration.WilsonOriginalNamedRoughRide
