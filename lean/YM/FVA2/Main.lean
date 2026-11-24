import YM.FVA2.Voice.Supply
import YM.FVA2.Handoff
import YM.FVA2.Notch.Duo
import YM.FVA2.Removal.Certified

/-!
# Formal-to-formal Wilson / MS-bar comparison

`wilson_to_MS` is the main result. It concerns the independent position prediction for the even-inversion orbit regulator.
Choose the stencils, lifts and tests once, apply the three diagram instructions,
and use the mass-independent N-frame. The comparison
concerns formal coefficients. Convergence of physical expectations along the
UV limit requires additional analytic estimates.

`Match` below spells out highlights of the result. Its `details : Voice.Supplied` field exports
an extensive further collection of theorems: for example

* `details.toServed.toPosted` for the **same** coefficients on the shared prescription, e.g.
  use `supplies` and `markT` there to state them via hierarchy transport, even in the common
  coupling. `Mission` (from `toPosted.toQuoted.toContract.toMission`) also exports the `Fk`
  connection (`herald`). See the dedicated modules `Facade`, `Hearth`, `Embr`, `Feyn`, `Slice`,
  `Orbit`, `Change`, `Voice/Encore`, etc. for stepwise/open
  field/denominator/gauge/source identities.
* `details.estimates` for stronger geometry and separated costs for mesh and volume (it and
  `Removal` concern among other things the *source-dependent* canonical undo error). See
  `Removal/{Wires,Certified}` for extracting some of the intermediate derivative estimates.
* `details.method` for the realization of the operator implementation including strict rank
  budget, and `details.normative` for results including the generators of scale transformations.

`batchFromEpochFk` provides a supplemental internal formula: also read the exact
initial batches (and point kernels) from the prescribed `Fk` open-conditional values, even
when working with finite-order truncations. Key to that assertion is the transfer with
field-dependent denominator and the later **different** common vacuum series; see
`YM/FVA2/Handoff{.lean,/Closure.lean}` for the explicit values and choices of roles and data.
It uses the specific `Fk`-data constructions (`Embr` etc.), not a claim of invariance under
choosing a different geometry or about texture/local estimates on these `Fk` preparations.

`dial` below tells which of the two (supplied) YM.MS endpoints to take a raw-sector
witness from. We use *their* geometries and `PhysicalSum`, prove identities and apply both of
those endpoints; we also prove the needed extension of that comparison (incorporates the W
shifts among these same stencils; no change of target predicate or MS continuum prescription).
**True** in `PhysicalSum` is the inversion regulator; this is *not* the `dial` flag. No claim
that the witness tables giving the (regulator-dependent) matching in these different
applications are all identical. But note `matchingTeam`.

In the public interface here `ν` is the **log scale parameter** (the y variable of the supplied
MS formalization; use `Teller.logNu μ` for MS-bar mass parameter `μ>0`).
E.g. see `Voice.Supplied.mass_unit`.
No other dim-reg or projection convention is meant.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Main

open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open Filter Set Function
open Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl.Near MS.Rake MS.Land
open Arrival Scale
open Scale.Facets (actMark couple)
open scoped Classical Topology

variable {G : Gauge} (N : WilsonPrescription G) (h : G.Simple)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S : Prescription (Press.portDeck G))

/-- The MS comparison, for the concrete physical operator sector (basis)
and extension specified in this
formalization. Uses formal series at each finite field horizon (so, in particular, expansion
order by order doesn't choose new parameters). Convergence statements are coefficientwise.
E.g. the bounds using `Speed.Strength` and `Speed.Labor` are by a constant times a fixed
strictly positive power of mesh spacing (`mildG`); the constant is independent of mesh and
center/profile on the indicated fixed-compact sets with test norm budgeting. `Front` implements
the joint cutoff limits for these bounds; in particular they hold on our concrete `run` (and we
state a test-wise limit along this schedule explicitly, for convenience).

Full connected and ordinary product comparisons exported. `Tide/Dial`: use *all* sets of marks,
not just empty or singletons. Empty-input ordinary product = 1; connected arrays normalized by
zero on empty. (Not an estimate on extensive vacuum constants.) `Strength/Labor` versions below
use ordinary product, every arity; here `d` is field horizon, `n` arity, `k` perturbative order;
`Tags G d n` uses the concrete `shellSector` physical fields (curvature-Wick basis).

`Time` arguments of the scale/OPE assertions are logarithmic. `Laws` includes both scale laws
and their intertwining by this same f,Z (including the beta transformation). `O.Canon.Supplied`
includes `Physical` (separated far and near exterior characterizations on the Wilson & MS sides,
powers-and-logs scaling/dilation, OPE estimates) and the field and coupling substitution
on the concrete formal OPE arrays. See also `O.Canon.Physical.kxcoeff` for the corresponding far test
matrix readout theorem. That limit uses continuum correlations: UV limit first, OPE (far- or
short-distance) limit afterwards. No UV estimate simultaneous in unbounded exterior scale,
shrinking separation and mesh claimed.
-/
structure Match (dial : Bool) : Prop where
    details : Voice.Supplied N h T S dial

    packets (i B : ℕ) : Nonempty (Handoff.Directory N i B)
    /-- This method is at every allowed finite order (increase `B` to increase that range).
    Same `N.serial`. Kernel in physical units (cover layout `x` still in
    lattice units). No further rank/test restriction
    from using this way of computing the vertex system here. These batches/points are before
    the subsequent (prescribed) position solve and coupling change. -/
    batchFromEpochFk (i B : ℕ) (P : Handoff.Directory N i B)
      (d k n : ℕ) (x : Fin n → Cover) (a : Test n) (p : Tags G d n)
      (_ : Handoff.Directory.budget G n d + k ≤ B) :
        litP N.scheme d (N.run.step i) (wrap (N.run.step i).p.side ∘ x) k p =
          ∑ t : Fin n → Dframe.Toon G d,
            Dframe.each t p * PowerSeries.coeff k (P.point_fk n d t x) ∧
        batch N.scheme (N.run.step i) d k n a p =
          ∑ t : Fin n → Dframe.Toon G d,
            Dframe.each t p * PowerSeries.coeff k (P.sweep_fk n d a t)

    matchingTeam :
      S.team = (Continuum.Continuation.proofStart h (Reg.supplies N.scheme T) dial).team

    /-- `Herald` at the literal supplied endpoint (`Continuum.Twin`: both Tide and Dial);
    `Completed` in the extension to exactly the W-subtracted columns. -/
    compared {W I : Type} [LinearOrder W] (p : Dial.Trial I W) (l : Filter I) (ν : ℝ)
      (u : W → Label (Press.portDeck G)) : Dial.Uses p l ν →
        (∃! Z, Voice.Ticket.Herald N h T p u l ν dial Z) ∧
        (∃! Z, Voice.Ticket.Completed N T S p u l ν Z)

    /-- The same coefficients exactly realize the MS input (no scaling limit).
    `Top.value` reassembles from the independent Wilson moments `Birth.words`. -/
    exactAtCutoff {W : Type} [LinearOrder W]
      (side : Side) (even : Even side.val) (s : Finset W) (d : W → Cover) (x : Cover)
      (η : ℝ) (u : W → Label (Press.portDeck G)) :
        PhysicalSum G S.team η side true s d x
          (ApplyMF (Press.wickInput N.scheme) (Stripped S.team) S u)
          (Top.value N.scheme u S x d side η s)

    /-- Meshes on the concrete schedule eventually satisfy each `Front` filter request. -/
    onSchedule : Tendsto N.run.step atTop Front

    /-- Separated point and test estimates after inserting the regulator-dependent
    matrix `Dframe.D` in the MS variable. `meteor` is the multilinear packaging of `MS.Dial.tour`. -/
    exactbreg (ν : ℝ) (n d k : ℕ) (p : Tags G d n) (K : Set (Points n)) :
      IsCompact K → K ⊆ conf n →
        Speed.Strength K (fun x => Dframe.postedPoint ν N.scheme S d x k p)
          (fun x => Dframe.meteor ν T d x k p) ∧
        Speed.Labor K (fun m a => Reg.Pivot.posted ν N.scheme S d m k n a p)
          (fun a => Reg.CoverTest.Rates ν T d k n a p)

    /-- This proof actually gets *exact* identity in order zero for this scheme. -/
    D_initial (ν : ℝ) (d : ℕ) (m : XSpace.Mesh) :
      PowerSeries.constantCoeff (Dframe.D ν S m d) = 1
    /-- The position solve, including *exact* equality at finite regulator -- no error
    need be estimated after multiplication by a possibly very large matrix. -/
    cancelsBare (ν : ℝ) (d : ℕ) : ∀ᶠ m in Front,
      Reg.Pivot.Ready ν N.scheme N.store S d m ∧
        Program.substitute (Dframe.reset ν S m) (N.store.opens N.scheme m d) =
          Reg.Pivot.coupledBatch ν N.scheme N.store S d m

    /-- `f` is the inverse of the concrete measured position coupling (`Measure.chi`). `Tangent`
    means real with vanishing order-zero coefficient & order-one coefficient one; `Token.Payment` includes
    both inverse identities. -/
    positionCoupling (ν : ℝ) :
      Tangent (Measure.f N.criterion ν T) ∧
      Reg.Token.Payment (Measure.chi N.criterion ν T) (Measure.f N.criterion ν T)
    /-- Position prescription really succeeds. -/
    detectorWorks : ∀ᶠ m in Front, PowerSeries.coeff 1 (Rose.chosen N.scheme N.criterion m) ≠ 0
    startsInX (d : ℕ) :
      Measure.Aim N.scheme N.criterion d (Measure.start N.scheme N.criterion d)

    /-- `Z` (`Measure.Z`, including the mass-independent `N` frame) is near identity, real,
    unit- and symmetry (signed axes) preserving, exactly grade preserving. -/
    frame (ν : ℝ) (d : ℕ) :
      Scale.Base (Measure.Z N.scheme N.criterion ν T d) ∧
        Native (Measure.Z N.scheme N.criterion ν T d)
    /-- Compatibility under horizon inclusions. -/
    frameCompat (ν : ℝ) (a b : ℕ) (H : a ≤ b) :
      Scale.Walk H (Measure.Z N.scheme N.criterion ν T a) (Measure.Z N.scheme N.criterion ν T b)

    /-- Conversion on all separated configurations. `couple` means substitute f(t),
    `actMark` means insert the columns of Z everywhere. -/
    eqconv (ν : ℝ) (d : ℕ) :
      actMark (Measure.Z N.scheme N.criterion ν T d)
          (couple (Measure.f N.criterion ν T) (Equator.wave ν T d)) =
        Measure.outlook N.scheme N.criterion d

    /-- `System.Readout` = smear of that same transformed MS continuum expression. -/
    transformedTest (ν : ℝ) (d : ℕ) : Jury.Verdict
      (actMark (Measure.Z N.scheme N.criterion ν T d)
        (couple (Measure.f N.criterion ν T) (Equator.wave ν T d)))
      (Scale.System.Readout N.scheme N.criterion T ν d)
    /-- It is the limit of the corresponding Wilson position prediction. Stronger uniform
    estimate before taking limit in `uniformTest`. -/
    wilsonLimit (ν : ℝ) (n d k : ℕ) (p : Tags G d n) (a : Test n) :
      Tendsto (fun i => Scale.System.positions N.scheme N.criterion d (N.run.step i) k n a p)
        atTop (𝓝 (Scale.System.Readout N.scheme N.criterion T ν d k n a p))
    uniformTest (ν : ℝ) (n d k : ℕ) (p : Tags G d n) (K : Set (Points n)) :
      IsCompact K → K ⊆ conf n →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : XSpace.Mesh in Front, ∀ a : Test n, tsupport a ⊆ K →
          ∀ b : ℝ, TestBudget.Bound a b →
            ‖Scale.System.positions N.scheme N.criterion d m k n a p -
                Scale.System.Readout N.scheme N.criterion T ν d k n a p‖ ≤
              b*C*m.spacing^MS.Tide.mildG

    uniqueConversion (ν : ℝ) (p : PowerSeries ℂ) (Z : Frames G) :
      Tangent p → (∀ i, Scale.Base (Z i)) →
        (∀ i, actMark (Z i) (couple p (Equator.wave ν T i)) =
          Measure.outlook N.scheme N.criterion i) →
        p = Measure.f N.criterion ν T ∧ Z = Measure.Z N.scheme N.criterion ν T
    dilation (ν : ℝ) : Scale.System.Laws N.scheme N.criterion T ν
      (GroupS.ψ N.criterion T ν) (GroupS.Ψ N.criterion T ν)
      (GroupS.gaugeN N.scheme N.criterion T ν) (GroupS.gaugeM N.scheme N.criterion T ν)
    separatedOPE (ν : ℝ) : O.Canon.Supplied N T ν

private lemma package {dial : Bool} (hS : Voice.Supplied N h T S dial) : Match N h T S dial := by
  let quoted := hS.toServed.toPosted.toQuoted
  have contract := quoted.toContract
  let input := contract.toMission.born
  have hf : Tendsto N.run.step atTop Front := goesFront (Expense.Stretched.runs _)
  refine {
    details := hS
    onSchedule := hf
    packets := fun i B => Handoff.Directory.always N i h B
    batchFromEpochFk := fun _ _ P d k n x a p hp =>
        ⟨ Handoff.Directory.lit_exact n d p P x k hp, Handoff.Directory.from_fk n d p a P k hp⟩
    matchingTeam := hS.maximum
    compared := ?_
    exactAtCutoff := ?_
    exactbreg := ?_
    D_initial := fun ν _ m => Dframe.Silver.dawn ν N.scheme S m T h input.Taylor input.still
    cancelsBare := ?_
    positionCoupling := fun ν => ⟨contract.cpl ν, (contract.toMission.pays ν).cost⟩
    detectorWorks := Rose.usable N.scheme N.criterion h
    startsInX := ?_
    frame := fun ν d => ⟨(contract.joint ν d).1, (contract.joint ν d).2.1⟩
    frameCompat := fun ν _ _ H => (contract.sees H ν).1
    eqconv := contract.series
    transformedTest := ?_
    wilsonLimit := ?_
    uniformTest := ?_
    uniqueConversion := contract.uniques
    dilation := contract.scales
    separatedOPE := hS.ope
  }
  · intro W I inst p l ν u hp
    exact Voice.Ticket.posting N h T S p u l ν hS.toServed dial hp
  · intro W inst side even s d x η u
    exact Top.tallies N.scheme u S x d side η s even
  · intro ν n d k p K hK hsub
    refine ⟨?_, Speed.Star.scope ν N.scheme T S h input.Taylor p hK hsub k⟩
    exact Speed.cartel.mpr ((Speed.Star.sharp ν N.scheme T S h input.Taylor p hK hsub k).sails)
  · intro ν d
    filter_upwards [contract.toMission.toSchemeV.prepared ν d] with m hm
    exact ⟨hm, Reg.Pivot.rulers ν N.scheme N.store S m hm⟩
  · intro d
    have he := Measure.reaches N.scheme N.criterion (Teller.logNu 1) T S h
      input.Taylor input.still input.base d
    rwa [Measure.together N.scheme N.criterion _ T S h input.Taylor input.still input.base] at he
  · intro ν d
    rw [contract.series ν d]; exact (contract.smear ν d).1.exact
  · intro ν n d k p a
    exact ((contract.smear ν d).2 k n a p).comp hf
  · intro ν n d k p K hK hsub
    exact ((quoted.funds p ν K hK hsub).checks k).2.1

/-- Main theorem: formal-to-formal Wilson-to-MS-bar comparison.
Comparison of physical expectations in a constructed QFT with this independent formal
prescription requires a separate analytic estimate. -/
theorem wilson_to_MS (dial : Bool) : ∃ S, Match N h T S dial := by
  obtain ⟨S, hS⟩ := Voice.physical_compare N h T dial
  exact ⟨S, package N h T S hS⟩

/-- Existence also without any setup-data hypotheses on the position prescription or MS
construction. The spacing/volume schedule `L` is arbitrary from `XSpace.Run`. -/
theorem solution (G : Gauge) (h : G.Simple) (L : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
        (S : Prescription (Press.portDeck G)), N.run = L ∧ Match N h T S dial := by
  obtain ⟨N, T, S, hl, hS⟩ := Voice.provision h L dial
  exact ⟨N, T, S, hl, package _ _ _ _ hS⟩

/-- Sample application with nonabelian gauge group given by `SUtwo` (det=1 in U(2)), and
`Notch.stair` (ratio 3, bounded terminal side, squared-log scale period growth). -/
theorem su_two :
    let G := Next.Foundations.SUtwo
    ∃ (N : WilsonPrescription G)
        (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
        (S : Prescription (Press.portDeck G)), N.run = Notch.stair ∧ Match N Trace.Col.duo T S true :=
  solution _ Trace.Col.duo Notch.stair true

end YM.FVA2.Main
