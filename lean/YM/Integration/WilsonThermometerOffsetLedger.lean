import YM.Integration.WilsonThermometerOffsetTrajectory

/-! The earned ultraviolet wallet and its numerical price on the same original
own-residue graph, before the choice of a cutoff, mark, or volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetLedger
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

def cash (d m : ℕ) : ℝ := ash G d (R.alloy.B.a.clock.J m) R.metals.p.profile R.y

include hG
private theorem stamps (shop : RG05Preconstruction.ReadoutPurchase R.b) (d : ℕ) :
    ∀ᶠ m in atTop, ∀ p N : ℕ, ∀ h : m<N,
      SignedPrice R.family m p d N (R.doors N p m h) (cash R d (m+1)) (cash R d m) := by
  let A := R.alloy.B.a
  let C := R.family
  let V := R.metals.p.profile
  let pay (d i : ℕ) := ash G d (A.clock.J i) V R.y
  have profile (i : ℕ) : A.params i = V (A.clock.J i) := params_eq R.alloy.B.valid i
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


theorem original (shop : RG05Preconstruction.ReadoutPurchase R.b) (d : ℕ) :
    ∀ᶠ m in atTop, RG05Readout.Address.Awake (C:=R.family) R.doors (cash R) m d ∧
      1 ≤ cash R d m ∧ cash R d m ≤ 1+Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta m)) := by
  let A:=R.alloy.B.a
  have cap (n : ℕ) : (R.family.path.levels.params n).columns ≤ cash R d n := by
    change (A.params n).columns ≤ _
    rw [params_eq R.alloy.B.valid n]
    exact (cash_fill G d (A.clock.J n) R.metals.p.profile R.y).choose_spec.2.1
  obtain ⟨n,quotes⟩ := eventually_atTop.mp (stamps R hG shop d)
  filter_upwards [eventually_ge_atTop n,A.fits.deep.eventually_ge_atTop d,
    (eventually_all_finset (Finset.range (d+1))).mpr (fun i _ => eventually_ge_atTop (R.family.ref i))]
    with m hn level delays
  refine ⟨⟨fun j hj => delays j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)),
    fun j _ => cap j,fun p j N hj => quotes j (hn.trans hj) p N⟩,
    (cash_fill G d (A.clock.J m) R.metals.p.profile R.y).choose_spec.1,?_⟩
  let s:=A.clock.J (m+1)
  have published := (shop.crossed s (A.clock.J m) d (step_paid A m).1 level).supp
  have nonneg : 0≤cash R d (m+1) :=
    zero_le_one.trans (cash_fill G d s R.metals.p.profile R.y).choose_spec.1
  have generous : cash R d m ≤ lamp (R.rolls.L s) s :=
    (le_add_of_nonneg_left nonneg).trans published
  have width : 1 ≤ ((R.rolls.L s).val:ℝ) := by exact_mod_cast (R.rolls.L s).property
  have easing : (1:ℝ)/((s:ℝ)+1) ≤ 1 := (div_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) s])
  apply generous.trans
  calc
    _ ≤ ((R.rolls.L s).val:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le width easing
    _ = ((A.S.block m).val:ℝ) := by rw [Real.rpow_one,Push.PriceCompiler.block_eq R.alloy.B.valid m]
    _ ≤ _ := shop.preMesh m

end YM.Integration.WilsonThermometerOffsetLedger
end
