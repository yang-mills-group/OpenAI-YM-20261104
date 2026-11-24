import YM.Integration.WilsonCenteredFourOutputReading
import YM.Integration.WilsonCenteredFourOutputBranch
import YM.Integration.WilsonCenteredNestedTreeWindow

/-! The single retained measured row on the real two-scale binary tree.
The other deposited channels remain in the ordinary chord. The charged
outer signed row is evaluated on the actual emitted actor and running
coupling at its own date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputTreePrice
open Filter Set MeasureTheory Spec Extraction Table Lattice Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Scale FVA2.Register FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open Next.Rank OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription RG12 RG17 SharpGram Climb PhysMS Trace.Pilot
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonCenteredFourOutputSensor WilsonCenteredFourOutputBranch WilsonMacroscopicDetector WilsonMSDictionaryVector
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedRawPair WilsonCenteredNestedProgram
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {hG:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool} (M:Main.Match Z hG T σ dial)

private theorem twoRows {X X' Y Y':ℂ} {e B:ℝ} (small:‖X-X'‖≤e) (outer:‖Y‖≤B) :
    ‖X*Y-X'*Y'‖≤e*B+‖X'‖*‖Y-Y'‖:=by
  rw [show X*Y-X'*Y'=(X-X')*Y+X'*(Y-Y') by ring]
  refine (norm_add_le ..).trans ?_
  rw [norm_mul,norm_mul]
  exact add_le_add (mul_le_mul small outer (norm_nonneg _) ((norm_nonneg _).trans small)) le_rfl

local notation "d₄" => (fun _:Fin 2=>4)
variable (g:ℝ→ℝ) (v:Fin 2→RG17.Free R.family 4) (c:Q.channels 4) {D:ℕ} (included:4≤D)
    (other:S.Tag) (m:ℕ) (out:Q.channels m)
local notation "pupils" => (placed F Q (tip F Q included c) other)

theorem original {U:Campaign R} (W:Campaign.Pillars R U) {b:ℝ}
    (source:FundedOriginalProperties.{u} hG b W) (pace:WilsonWindowReportingPace.Slow R.kit) {b₀:ℕ} (bp:0<b₀)
    (fac:OPE.Facilities R.family f S) (leading:PhysMS.Leading F J) {A:(Bel R.family.book).Hierarchy}
    (obedient:∀d:ℕ,∀ᶠ r in trail,PhysMS.Frame.obedient F A (J r) d)
    (l:Ultrafilter (ℕ×ℕ)) (lo:(l:Filter _)≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    {K:Set (Points 2)} (compact:IsCompact K) (apart:K⊆conf 2) (hg:Coupling G g)
    {radius η:ℝ} (Rn:0≤radius) (ηp:0<η):
    ∃j:ℕ,∃ L:ℝ,0≤L ∧ ∀(b q:ℕ) {ε:ℝ},0<ε →
      (∀ᶠ r in trail,∀ψ:Test 2,tsupport ψ⊆K → ∃ᶠ s:ℝ in atTop,
        let z:=WilsonCenteredFourOutputReading.delta F Q J Z T ν M g v c q ψ r s
        |z.re|≤ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖) ∧ |z.im|≤ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖)) →
      ∀ᶠ r in trail,∀ ψ:Test 2,tsupport ψ⊆K → ∀ (y:Fin 2→E4) (o:E4),y 0=0 →
        let t:=WilsonThermometerWeakPairClock.scale g b r
        (∀i,‖y i-o‖≤radius*t) → (∀i k,i≠k → η*t≤‖y i-y k‖) → ∀A:Rule F Q,
        let X:=grade F Q c (J r 4 (prediction R.family d₄ 4 Z T ν v ψ q (g r)))
        let N:=A 2 m out t (g t) y pupils o
        ‖heard F Q included c m out (fun i=>J r 4 (v i)) other r ψ y o-X*N‖ ≤
          ((‖grade F Q c‖*fee F 4+2)*ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖))*
            (L*shell t^j*(t^m/(t^4*t^other.1))) + ‖X‖*‖express Q m out y pupils o-N‖ :=by
  obtain ⟨_,logged⟩:=WilsonCenteredNestedElection.on_ticket R F Q fac l lo ticket
  obtain ⟨j,L,Ln,salary⟩:=WilsonCenteredNestedLoggedRow.original F Q fac.toServices logged.toSingleLog
    pupils m out Rn ηp
  refine ⟨j,L,Ln,fun b q ε ep signed=>?_⟩
  have near:=WilsonCenteredFourOutputReading.original F Q J Z T ν M g v c q W source pace bp
    fac leading obedient compact apart hg ep signed
  have outer:=(WilsonThermometerWeakPairClock.small hG g hg b).eventually salary
  filter_upwards [near,outer,WilsonCenteredFourOutputBranch.original F Q fac.toServices compact apart] with
    r actual coarse joined ψ supp y o center t ball distance A
  rw [joined included c m out (fun i=>J r 4 (v i)) other ψ supp y o center]
  apply twoRows (actual ψ supp)
  have bill:=coarse y o ball distance
  rw [Fin.prod_univ_two] at bill
  exact bill

end YM.Integration.WilsonCenteredFourOutputTreePrice
