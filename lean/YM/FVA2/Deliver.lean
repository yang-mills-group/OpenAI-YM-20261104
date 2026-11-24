import YM.FVA2.SpringUniq
import YM.FVA2.CommonWitness
/-!
# Top-level theorem of the FORMAL-TO-FORMAL project. Stage: **SEPARATED CORRELATIONS**

Starts from precisely the X comparison procedure/inverse MS scheme, ends at those arrays and
universal conversion f,Z. Input sector and dependencies are genuine.YM.THIS file provides also all-choice
interpretation of finite reg results (formal-to-formal stage not actual comparison).

 * Adds companion's common-choice supplier with ONE prescription. Link.T.Foundations.Basis common locks.
 * Estimator reading stage for position kernels power accuracy simultaneously.Profiles all.
 * Regulator scope: uvLimit plus growing inversion period **along admissible joint schedules**.
   `Standard.accuracy` here specifically unrestricted order q (can take powers of 3 arbitrary big)
   of the supplied ε_N geometry with center `origins`, epsilon. Also upper Visa estimates on
   qualified trials for the pre-position scheme; **NOT** asserting commutative arbitrary limits
   or substitution of already shrinking nonscheduled moving arrays. "any order" ⇒ fixed n, profiles.
 * Gauge scope: see `Interface`. all uses standard oriented graph Piece. No cover substitution.

This does NOT claim an OPE extraction theorem or the full perturbative matching theorem. In particular,
this supplier doesn't compare with local analytic comparison kernels. For that task use the
bundled witness and independent prescription definitions on shared spine. Other realization
calculations can apply this theorem to those predictions. Intertwines scale and β laws; no assertion
of their explicitly computed order-3 values. Distinguish clock modulus from inverse-length arrays ν; Φ_y.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Atoll.Main
open Filter Topology Set Function MeasureTheory
open MS MS.Pearl MS.Train MS.Hem.Mell MS.Outlook MS.Land MS.Vane MS.Latch MS.Rake MS.Tide MS.Dial MS.High MS.Menus MS.Book MS.Book.Program MS.Book.Convolve
open BoxOffice ColorCode Sail Pic Forge Panel Verne Strat Hop Parity Plot Erase Clock WorldJet Attend ArchTurn Blaze Frost Esprit
open Pert Pert.Position Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Bend PositionX.Bare.Shop Elegant Lattice
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}
-- any fixed-block hierarchy fits at a point with chosen schedule (q=3^*). use power.From
namespace Schedule
open RG IteratedWilsonPrescription
lemma gradeAt (P:RG.Patch)(i:ℕ): PertExtension.LatticePT.side P.L i= gradeSide P (i+i*i+1):= ( Pond.times P.L i|>.symm ).trans ( Subtype.ext (Pond.fullSide ..))
-- use any κ from the common kernel choices. E transport exact.
def atGauge (P: Patch)(κ:KernelChoices)(H:P.Branches κ G)(k:ℕ): IteratedWilsonPrescription G (PertExtension.LatticePT.side P.L k):= (gradeAt P k).symm ▸ IteratedWilsonPrescription.ticket P κ H _ -- t shape
-- e.g.
def frameGauge (P:Patch)(κ:ℝ) (h:0<κ)(G:Gauge)(n:ℕ): IteratedWilsonPrescription G (PertExtension.LatticePT.side P.L n):= atGauge P (Next.Foundations.kernel G κ h) ( Next.Foundations.branches G κ h P ) n
end Schedule
open PertExtension.LatticePT (side epsilon origins Grid.sample)

structure PowerAccuracy (G:Gauge)(h:G.Simple)(V:Warehouse G)(B: Booked (wings G)) (P:Land.Prescription (wings G))(A: MS_Data G (angular B V))
    (HV:ExactSpin V P) (HI: Trusted P){t:ℝ}(T:Booth t V.F): Prop where
   smooth_live (s:ℝ)(d n:ℕ) (v: Pert.Position.Section V.F d)(q:ℕ+)(hq:1<q.val): Prow.Tandem atTop ( Fountain.feel q ) (fun i=>lookie V.F v ( unglue V P HV HI q s i d n )) (fun _=>lookie V.F v ( Spring.ms V A s d n )) ( lookie V.F v ( Spring.ms V A s d n ))
   precise (s:ℝ)(d:ℕ)(q:ℕ+)(hq:1<q.val): Prow.Gold atTop ( Fountain.feel q ) ( fun i=> Bend.renormal (warehouse V) q h T i d ) (fun _=> (Pic.X V h A s T).lives d ) ((Pic.X V h A s T).lives d)
   ordinary : ∀ (n d k:ℕ) (s:ℝ)(p:Fin n→ E V.F d)(R:Set (Points n))(_: R⊆ conf n)(_: IsCompact R)(q:ℕ+)(_: 1<q.val), ∃ C:ℝ,0<C ∧∀ᶠ i in atTop,∀ o∈ origins q i,∀ u: Fin n→ Site ( PertExtension.LatticePT.side q i ), Grid.sample q i u∈R → dist (PowerSeries.coeff k ( Fountain.tuition V P HV HI q i s o u d p)) ( (Pic.marked V A s).off d (Grid.sample q i u) k p ) ≤ C*Fountain.feel q i -- binder syntax
   hard : ∀ (n d k:ℕ) (s:ℝ)(p:Fin n→ E V.F d)(R:Set (Points n))(_: R⊆ conf n)(_: IsCompact R)(q:ℕ+)(_: 1<q.val), ∃ C:ℝ,0<C ∧∀ᶠ i in atTop,∀ o∈origins q i,∀ u: Fin n→ Site ( PertExtension.LatticePT.side q i ), Grid.sample q i u∈R → dist (Elegant.counter h V q i T o u d k p) ( (Pic.X V h A s T).off d (Grid.sample q i u) k p ) ≤ C*Fountain.feel q i
-- covers stronger fax estimated from Startup proving.Frame.
variable (h:G.Simple)(V:Warehouse G) (B: Booked (wings G))(A: MS_Data G (angular B V)) (P:Land.Prescription (wings G))(HS: ExactSpin V P)(HU: Trusted P) {t:ℝ}(T:Booth t V.F)
variable (C:Concord h V B A P HS HU T)
include C
lemma Production : PowerAccuracy G h V B P A HS HU T := by
   refine ⟨ fun s d n p q hq=> start_power V P A HS HU C.rates q hq s ( l:=atTop ) ( f:=id ) tendsto_id d p n,fun s d q hq=> ?_, fun n d k s p R hM hc q hq=> ?_, fun n d k s p R hM hc q hq=>?_ ⟩;
   · simp_rw [Pic.XL]; exact endpoint_power h V P A HS HU C.rates q hq s (f:=id) tendsto_id T ( C.born q hq ) d
   · obtain ⟨c,hc,hF⟩:= Fountain.rate_point V P A HS HU C.rates q hq s hM hc k p; exact ⟨c,hc,hF.mono (fun i H o ho u hu=> by rw [Pic.readMark V A s k d n _ (hM hu) ]; exact H o ho u hu )⟩
   obtain ⟨c,hc,H⟩:= Elegant.rate_points h V P A HS HU C.rates q hq s T ( C.born q hq ) hM hc p k; exact ⟨ c,hc,H.mono (fun i H o ho u hu=> by rw [ Panel.sees _ (hM hu) ]; exact H u hu o ho) ⟩
omit C
local notation "Θv" s=> Forge.transfer V A T s
structure Economy : Prop where
   paid : Concord h V B A P HS HU T
   ready : PowerAccuracy G h V B P A HS HU T
   schema : RadL.Reg (angular B V)
   inputs : ∀ (q:ℝ), Clock.rate P.team q= PowerSeries.X * Clock.expanded q (Clock.looped P.team)
   boundary : ∀ (k:ℕ) x y,x ≠ 0→ Counterpart.bareD V P x y 0 k= 1
   costs : ∀ d n (i:Owner G d)(j:BasisIx G d),( P.fees d i n ).register j ≠0 → ∃ k:ℕ, n+( Land.read i).grade=j.grade+2*k
   hymns (y:ℝ) : let I := Pic.X V h A y T; ∃ S:Pic.pass V h A T,
       let p:= Forge.transfer V A T y S
       Unity V h A T y p I ( Forge.chooseN V A T y S ) ∧ sloping p ∧ Aspect ( Pic.marked V A y ) ∧ Aspect ( Forge.Check V A T y S ) ∧ (∀ d:ℕ, Jet.ren (Elegant.ξ h V A y T) ( I.lives d )=( Panel.flip (Pic.marked V A y) ( Pic.L V A y h ) ).lives d)
   both : ∃ D:Land.Prescription (wings G), Matched.AllProfiles A ( V.diction (wings G) ) D ∧ D.team=P.team
open PertExtension.LatticePT (Word)
-- lemma helpers explicit
lemma unityEco (D:Land.Prescription (wings G))(hV:Matched.AllProfiles A (V.diction (wings G)) D)(hQ:P.team=D.team)(hB:RadL.Reg (angular B V)) (C:Concord h V B A P HS HU T): Economy h V B A P HS HU T where
   paid:= C
   ready:= Production h V B A P HS HU T C
   schema:= hB
   both:= ⟨ D,hV,hQ.symm ⟩
   inputs := let q:ℕ+:=3; price_g V A T P HS HU C.rates (q:=q) (by decide) ( C.born q (by decide) )
   costs := let q:ℕ+:=3; fare_pair V A P HS HU T (q:=q) (by decide) ( C.born q (by decide) ) (overbook ..) C.rates.1
   boundary :=fun _ x y h=> Erase.solo V A P HS HU C.rates x y _ h
   hymns := fun y=> by intro I; let S:= Pic.supplies V T A _ _ _ C; refine ⟨ S,?_⟩; intro p; refine ⟨ characterized V h A T y S ( C.born _ (by decide) ), turnZ V A T y S, Plot.Real_v V A P HS HU C.rates,( Plot.clarity_s V A T P HS HU C.rates S ).2, Pic.payX V A T S y ⟩ -- syntax
-- uniqueness. extend doc tasks.Clock. Persist both calls.
include h
lemma accounts (D:Land.Prescription (wings G))(hV:Matched.AllProfiles A ( V.diction (wings G) ) D)(hB:RadL.Reg (angular B V)) : ∃ (P: Land.Prescription (wings G))(T:ExactSpin V P)(H: Trusted P)(k:ℝ)(R:Booth k V.F), Economy h V B A P T H R ∧ P.team=D.team := by
   obtain ⟨P,S,U,c,T,hP,hC⟩:= Sail.chooses h V B A D hV; exact ⟨ P,S,U,c,T,unityEco h V B A _ _ _ _ D hV hP hB hC,hP⟩
def Packing (V: Warehouse G) : Prop:= ∃ (B: Booked (wings G))(A: MS_Data G (angular B V)), RadL.Reg B ∧ ∃ (Q D: Land.Prescription (wings G)), Matched.AllProfiles A ( V.diction (wings G) ) Q ∧ Matched.AllProfiles A (V.diction (wings G)) D ∧ Clock.rate Q.team=Clock.rate D.team ∧ ∀ (Q':Land.Prescription (wings G)), Matched.AllProfiles A ( V.diction (wings G) ) Q' → ∃ (P: Land.Prescription (wings G))(T:ExactSpin V P)(H: Trusted P)(k:ℝ)(R:Booth k V.F), Economy h V B A P T H R ∧ P.team=Q'.team
-- explicitly both `fromDial` and `fromTide`. each proves AllPoints.
/-- Supplier on separated-points/PT (pure field sector, X-vs-MS from same specified labels). No assumption of the hypotheses of any analytic actual-theory comparison. Also applies to
  ANY Warehouse, nonempty.L. See companion stronger flavored method later.
 -/
theorem joint_M : Main.Packing h V:= by
    obtain ⟨B,hB⟩:= MS.RadL.picks ( ColorCode.wings G ); let A:= Classical.choice (bookedMS (angular B V)); have ht: RadL.Reg (angular B V):= RadL.radial V hB;
    obtain ⟨Q,hQ⟩:= Sail.fromTide h V B A; obtain ⟨D,hD⟩:= Sail.fromDial h V B A;
    refine ⟨ B,A,hB,Q,D,hQ,hD,?_,fun Q H=> accounts h V B A Q H ht ⟩; obtain ⟨ P,S,H,k,T,⟨K,L⟩ ⟩:= accounts h V B A Q hQ ht; obtain ⟨ P',S',H',k',T',⟨K',L'⟩⟩:= accounts h V B A D hD ht; rw [← L, ← L' ]; exact Plot.clock_eq V A T P S H K.paid.rates ( q:=3) (by decide) (K.paid.born 3 (by decide)) S' H' K'.paid.rates -- order assumption instance.Patch
-- user.Pitch
end YM.FVA2.Atoll.Main
namespace YM.FVA2.Atoll.Main
open Source Era MergeProof Atoll
-- the companion can import Install for use.Same.Datum.
theorem install {G:Gauge}(h:G.Simple)(κ:ℝ)(hκ:0<κ)(δ:PhysicalNext.Repeat.Daisy.Charity.RG12.Decal G)(F:Extraction.Order) : ∃ (C: Family G) (f:Extraction.Order)(T:Table C.book)(W:Spec.Final C (F.refine f) T)(L: EveryPhase.Almanac W)(A:UVExtension.Mast.Couture C h (LocalTaylorR2.Marigold.aetherD (LocalTaylorR2.Strange.jetEngine G) δ)), Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ∧ UVExtension.Oasis.Floral (hG:=h) C ∧
      ( Extraction.Order.mk Extraction.Sequence.full (F.refine f).per ).Ordered C T ∧ EveryPhase.Completed W L ∧ OPE.Facilities C ( F.refine f ) T ∧ LocalTaylorR2.Marigold.QuadPose ( LocalTaylorR2.Strange.jetEngine G ) A ∧ JointConstruction.ForcedStepControl C ∧ ∃ (hC: C.Makes) (hP:∀ i,Bid.pop ( C.localSection i )), Packing h (Atoll.share C hC hP) := by
    obtain ⟨C,f,T,W,L,A,hC,hCal,hP,h',hT,hL,hF,ha,hA⟩:= JointConstruction.localTaylor_with_forcedInheritance h κ hκ δ F; exact ⟨ C,f,T,W,L,A,hCal,hP,h',hT,hL,hF,ha,hA,hC,FormalOPE.RG10.supplies h',joint_M h .. ⟩ -- C implicit metav
end YM.FVA2.Atoll.Main
