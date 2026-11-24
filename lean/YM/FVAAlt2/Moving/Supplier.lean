import YM.FVAAlt2.Moving.Born
/-!
# Formal-to-formal correlation comparison

- Operates on a single concrete Run (with customary tied inputs through `Run.again`)
 including its witnesses on **all periods**, chosen before requests.
- `Top.Output`: Fixed-side (quantified) and limiting, constant-q and aperture positional normalization scheme & measured
 including coupling `f` and Framed C W with W the unique compatible rotation defined in
 `Mass.Output` (and agreement with `Rails` if using it). Applies native RG10 `Plan.collect`
 & CheckG=converted MS array cast. No Dense.Mark assumptions.
- Then READ actual moving mesh coefficients **using only ProgramT.Stamp & LocalFormal** before post-pose & higher-mark operations. `Matter` doesn't assume any answer, filled even if the position
 system is not yet regular (see `Study.officialCredential` etc for late-branch lemmas). `Funding.reach` identifies these coefficient TESTS
 with the same continuum perturbative answer (all labels, ANY real smooth separated profile,
 with smearing on real parts of tests; fixed µ while regulator θ varies) through each finite order. The auxiliary width Schedule `.hold_all` (∃ bound for regular-torus period for the LocalFormal calculation at stations) and Point uses on the MS.Dial side (Clearance) MUST still be respected; supplied existence, e.g. `bearings` & `fees`. Programs read through specified finite-order reclosures, not claims that the local Taylor comparison analytic errors admit such reclosures.
 Coupling fits of the nonperturbative trajectory/unknown analytical comparisons (another project) do NOT enter this result.
- Physical conversion.Eq is between the **formal correlation prescriptions**, not to claim radial approximation stability or coadmission with the hidden real-YM budgets. Own application of `Pegs.uniform` (from `MS`/Study comparison) supplies power error at finite spacings for separated MS shape point pixels, in the described schedules, through the indicated demands; gives quantitative bounds on regulators used here. Integrated coefficient conclusion not promising a rate for the final Riemann→integral step. Offsets center ONE in specified clearance geometry per setting. Real background β interpretation of any of the formal conversions/clocks not part of this result.

$ε=exp(-Θ)$ here remote sampling in lattice-spacing units (`Track`). The coordinate scale uses `μ` constant 
in the `MS_Data` reference conventions. Many other (e.g. clearance, thicker-period, etc.) variants of
 schedules may be costed separately; this result is not an estimate on an arbitrary diagonal.
 See proof path. This header is not asserting analytic comparison or OPE (separate, still need proof).
 Uses the standard Rig (leading frame from horizon-polynomial occupation; uses exactly Plan protocol).

-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Supplier
open Function Set Filter MeasureTheory Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT Pegs
open MS MS.Land MS.Menus MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open Integration RunFormalChain Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home YM.FVAAlt2.Home.Report
open Labels Extra.FD Maxwell Source Extraction FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop Perot Study
open RG10 RG10.Position RG10.Carryon YM.FVAAlt2.Moving.Budget
open PowerSeries (C coeff constantCoeff)
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{K:KernelChoices}{X:Type}
variable (Y:Oracle.Program K)(Z:∀ B:Patch,B.Branches K G)(C:Run G)(R:Lodge.Contract C Y Z) (t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B"=> (R.profile Y Z C t ht)
local notation "P"=> (Period.Field.LodgeT.instance_real Y Z C R t ht)
local notation "Γ"=> C.family.path
local notation "Φ"=> Study.Plan C
set_option quotPrecheck false
variable (l:Filter X) (μ:ℝ)
local notation "Y_" k:max=> ( B ).PoseT μ a k -- avoid free unbound
variable {J':Booked (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)}{H:MS_Data G J'} (τ:MS.Land.Prescription (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified))
local notation "Ξ"=> ( seats (Study.Plan C).liftOff (Study.Plan C).certified )
variable {D:Drivers} (r:Patience (Study.Plan C) D) (W: ∀ i:ℕ,Matrix ( RG10.Position.Deck C.family.labels i ) ( RG10.Position.Deck C.family.labels i ) (PowerSeries ℝ))
local notation "Ζ"=> (Mass.ζfinal (Study.Plan C) μ H)
variable (p:ℕ) (g:G.ColorIndex)(hG:G.Simple)[l.NeBot][l.IsCountablyGenerated]
structure Walk (l:Filter X)(x:X→ Cover)(F: Calibration.Tent ( ( R.profile Y Z C t ht ).entire ))(ℓ:X→ℕ) : Prop where
    region: ( R.profile Y Z C t ht ).VenueT x
    at_end : Study.Holding Y Z C R t ht F p τ μ ℓ l
variable (R0:Top.Output C.metals.O (Study.Plan C) H τ μ)
structure Funding (p:ℕ)(g:G.ColorIndex)(H:MS_Data G J')(μ:ℝ)(F:Calibration.Tent ( ( R.profile Y Z C t ht ).entire )): Prop where
    pillar : Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p
    bearings : ∃ x:X→ Cover,(R.profile Y Z C t ht).VenueT x
    fees : ∃ Λ₀:X→ℕ,∀ Λ:X→ℕ,(∀ᶠ x in l,Λ₀ x≤Λ x) → Study.Holding Y Z C R t ht F p τ μ Λ l
    reach (x:X→ Cover)(Λ:X→ℕ)(T:Walk Y Z C R t ht μ τ p l x F Λ)(I:Type) (_:Fintype I)(_:DecidableEq I)(i:I) (S: Marker.Census I) :
       Nonempty (ProgramT.Stamp Y Z C R t ht F p x S i) ∧ ∀ D:ProgramT.Stamp Y Z C R t ht F p x S i,∀ d:ℕ, ∀ v:Home.Datum (RG10.Position.Deck C.family.labels d),
       Nice p l (fun w=> ProgramT.Matter Y Z C R t ht F p Λ x S i D W w d v ) (mix ( ( Convert.f (Study.Plan C) μ H ).charge∘ Home.Report.science μ H C.family.labels d ) ( Mass.ζfinal (Study.Plan C) μ H d ) v )
    points (x:X→ Cover)(Λ:X→ℕ)(K:Walk Y Z C R t ht μ τ p l x F Λ) (n:ℕ)(E:Set (Points n))(T:IsCompact E)(hp:E ⊆ conf n)(D: Fin n→ Rake.Label ( seats (Study.Plan C).liftOff (Study.Plan C).certified )) : ∀ k:ℕ, k ≤ p→ ∃ C₁:ℝ,0<C₁∧∀ᶠ i in l,∀ q:Pegs.Motor (R.profile Y Z C t ht) n i,CalendarT.sample i q∈ E → Pegs.Error Y Z C R t ht F D τ H μ Λ x k i q ≤ C₁ * Sound.BudgetAir (R.profile Y Z C t ht) i
    slope (x:X→ Cover)(Λ:X→ℕ)(K:Walk Y Z C R t ht μ τ p l x F Λ) : Tendsto (fun w:X=> coeff 1 ( Convention ( Row ( Study.Rack₁ Y Z C R t ht F Λ x w ) (( Study.Plan C ).stock) ) ).x ) l (𝓝 1)
-- supply using actual canonical estimator
include R0 hG
lemma empowered (hV:Tendsto t l atTop)(Hq:∀ x,p ≤ t x)(hp:p≠0)(he:Mass.Framed (Study.Plan C) r W): ∃ F: Calibration.Tent ( ( R.profile Y Z C t ht ).entire ), Funding Y Z C R t ht l τ W p g H μ F:=by
 obtain ⟨F,H'⟩:= Calibration.tomorrows ( R.profile Y Z C t ht ).desk Y G Z g (Rocket.native _) p; refine ⟨ F,H',⟨ _,( B ).visible ⟩,Study.hold_all Y Z C R t ht F p τ μ l hV,?_,?_,?_ ⟩
 · intro x Λ K I _ _ i S; refine ⟨ProgramT.funds Y Z C R t ht F p x S i H', ?_⟩ -- likely ordering
   intro T b v; exact ProgramT.dataLimit Y Z C R t ht F p Λ x H' S i hG T r μ τ R0 W he b v l hV Hq K.at_end K.region (Nat.pos_iff_ne_zero.mpr hp)
 · intro x Λ K0 n E hE hx D j hj; let d:= ∑ i:Fin n,(D i).h; obtain ⟨σ,hσ,ht'⟩:= K0.at_end n d; exact Pegs.uniform hG Y Z C R t ht F p d D τ H μ Λ x hE hx l hV H' K0.region Hq R0.draw.high hσ ht' (fun i=>Finset.single_le_sum (f:=fun i=>( D i ).h) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)) j hj
 intro x Λ h; exact Study.near_s Y Z C R t ht F p μ Λ x l hV hG τ R0 H' Hq h.region h.at_end (Nat.pos_iff_ne_zero.mpr hp)
omit R0 hG [l.NeBot] [l.IsCountablyGenerated]
structure CorrelationMatch (Y :Oracle.Program K)(Z:∀ L:Patch,L.Branches K G)(C:Run G) (R:Lodge.Contract C Y Z){J':Booked (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)}(H: MS_Data G J')(T:MS.Land.Prescription (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)) : Prop where
    apply_M : ∀ μ:ℝ,Top.Output C.metals.O (Study.Plan C) H T μ
    tune : ∃ (D:Drivers)(p:Patience (Study.Plan C) D) (W:∀ i:ℕ,Matrix ( RG10.Position.Deck C.family.labels i ) ( RG10.Position.Deck C.family.labels i ) ( PowerSeries ℝ )), Mass.Framed (Study.Plan C) p W∧∀ (X:Type)(g:G.ColorIndex)(μ:ℝ)(l:Filter X) (_:l.NeBot) (_:l.IsCountablyGenerated)(t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x),Tendsto t l atTop→∀ n:ℕ, n≠0→ (∀ x,n≤t x)→∃ F:Calibration.Tent (( R.profile Y Z C t ht ).entire ), Funding Y Z C R t ht l T W n g H μ F
include hG
theorem supply_H : ∃ (A: Booked Ξ)(H:MS_Data G A)(T:Prescription ( seats (Study.Plan C).liftOff (Study.Plan C).certified)), CorrelationMatch Y Z C R H T:=by
 obtain ⟨A,H,T,hT⟩:= Top.in_room C.metals.O C.alloy.B.ratio hG (basisR C)
 let U:= Study.Plan C; let g:= (hT 0).credit Top.age; obtain ⟨N,h,-⟩:= (hT 0).tilt _ g
 exact ⟨ A,H,T, hT,Top.age,g,N,h,fun X g' μ l _ _ t ht Hξ n hm hk=> empowered Y Z C R t ht l μ T g N _ g' hG (hT μ) Hξ hk hm h ⟩ -- ordering check
-- User application. Includes nontrivial coverage: `Rocket/Poses` selectors satisfy VenueT, User can index along Options stamps ℕ etc; Scope Demand.For reconstruction `Run.again` exact existence on this same Run. 
theorem procurement {ε:ℝ}(he:0<ε) : ∃ (C:Run G)(K:KernelChoices)(Y:Oracle.Program K)(Z:∀ P':Patch,P'.Branches K G)(R:Lodge.Contract C Y Z),( C.family.path.levels.clock.kernel.penalty = ε ) ∧ Run.Ties C ∧ (∀ v:Extraction.Order, ∃ (w:Extraction.Order)(S:Table C.family.book), Nonempty ( Spec.Final C.family (v.refine w) S ))∧ (Nonempty G.ColorIndex) ∧ ∃ (A:Booked ( Home.seats (Study.Plan C).liftOff (Study.Plan C).certified ))(H:MS_Data G A)(T:MS.Land.Prescription ( Home.seats (Study.Plan C).liftOff (Study.Plan C).certified )), CorrelationMatch Y Z C R H T:=by
 obtain ⟨ C,K,Y,Z,R,h,u,U ⟩:= Lodge.Entry.start hG he; obtain ⟨hu,hv⟩:= Run.again C hG; obtain ⟨g,-⟩:=u
 exact ⟨ C,K,Y,Z,R,h,hu,hv,⟨g⟩,supply_H Y Z C R hG ⟩
end YM.RegulatorIR.FVAAlt2.Moving.Supplier
