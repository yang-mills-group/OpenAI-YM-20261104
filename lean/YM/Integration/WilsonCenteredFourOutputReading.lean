import YM.Integration.WilsonCenteredFourOutputSensor
import YM.Integration.WilsonMSDictionaryVector

/-! The signed physical measurement for a retained grade-four component
of two genuine grade-four inputs. Both signed readings use one finite far
date of the independent position-space experiment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputReading
open Filter Set MeasureTheory Spec Extraction Table Lattice Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Scale FVA2.Register FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonCenteredFourOutputSensor WilsonMacroscopicDetector WilsonMSDictionaryVector
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {hG:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool} (M:Main.Match Z hG T σ dial)

def panel : Read.Geology G 4:=((M.separatedOPE ν).wilson.light 4).choose

local notation "d₄" => (fun _:Fin 2=>4)
local notation "bank" => (panel Z T ν M)
variable (g:ℝ→ℝ) (v:Fin 2→RG17.Free R.family 4) (c:Q.channels 4) (q:ℕ)

def delta (ψ:Test 2) (r s:ℝ):ℂ :=
  let a:=fun i=>J r 4 (v i)
  let entry:= experiment R.family d₄ 4 Z T ν v ψ bank q (g r) s
  ∑ X:probes F 4,coefficient F Q c X*(RG17.appeared F (d:=d₄) a X.val r ψ-
    X.val.charge F 4 (J r 4 entry))

theorem raw (ψ:Test 2) (r s:ℝ) :
    delta F Q J Z T ν M g v c q ψ r s =
      pairRead F Q c (fun i=>J r 4 (v i)) r ψ -
      grade F Q c (J r 4 (experiment R.family d₄ 4 Z T ν v ψ bank q (g r) s)) :=
  (full_error F Q c _ _ _ _).symm

theorem far (ψ:Test 2) (r:ℝ) :
    Tendsto (delta F Q J Z T ν M g v c q ψ r) atTop
      (𝓝 (pairRead F Q c (fun i=>J r 4 (v i)) r ψ -
      grade F Q c (J r 4 (prediction R.family d₄ 4 Z T ν v ψ q (g r))))) :=by
  have ready : Read.Detected (Measure.outlook Z.scheme Z.criterion) bank:=
    ((M.separatedOPE ν).wilson.light 4).choose_spec.2
  have original:=experiment_limit R.family d₄ 4 Z T ν v ψ M bank ready q (g r)
  have move:Continuous (J r 4):=(J r 4).toLinearMap.toContinuousLinearMap.continuous
  have all:=tendsto_const_nhds (x:=pairRead F Q c (fun i=>J r 4 (v i)) r ψ) |>.sub
    ((grade F Q c).continuous.continuousAt.tendsto.comp (move.continuousAt.tendsto.comp original))
  exact all.congr (fun s=>(raw F Q J Z T ν M g v c q ψ r s).symm)

theorem original {U:Campaign R} (W:Campaign.Pillars R U) {b:ℝ}
    (source:FundedOriginalProperties.{u} hG b W) (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (bp:0<B)
    (fac:OPE.Facilities R.family f S) (leading:PhysMS.Leading F J) {A:(Bel R.family.book).Hierarchy}
    (obedient:∀d:ℕ,∀ᶠ r in trail,PhysMS.Frame.obedient F A (J r) d)
    {K:Set (Points 2)} (compact:IsCompact K) (apart:K⊆conf 2) (hg:Coupling G g) {ε:ℝ} (ep:0<ε)
    (signed:∀ᶠ r in trail,∀ψ:Test 2,tsupport ψ⊆K →
      ∃ᶠ s:ℝ in atTop,let z:=delta F Q J Z T ν M g v c q ψ r s
        |z.re|≤ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖) ∧
        |z.im|≤ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖)) :
    ∀ᶠ r in trail,∀ψ:Test 2,tsupport ψ⊆K →
      ‖grade F Q c (RG17.basket Q 4 (d:=d₄) (fun i=>J r 4 (v i)) r ψ)-
        grade F Q c (J r 4 (prediction R.family d₄ 4 Z T ν v ψ q (g r)))‖ ≤
      (‖grade F Q c‖*fee F 4+2)*ε*(g r)^q*r^4*(∫ x:Points 2,‖ψ x‖) :=by
  have physical:=WilsonMacroscopicDetector.original hG W source pace bp F fac Q J leading obedient d₄ v
    compact apart hg 4 q (σ:=1) zero_lt_one ep
  filter_upwards [physical,signed,RG17.positiveLength,hg.positive] with r price rows rp gp ψ support
  let a:=fun i=>J r 4 (v i)
  let m:=∫ x:Points 2,‖ψ x‖
  let aim:=ε*(g r)^q*r^4*m
  let modeled:=grade F Q c (J r 4 (prediction R.family d₄ 4 Z T ν v ψ q (g r)))
  have heard:‖pairRead F Q c a r ψ-modeled‖≤2*aim:=by
    apply le_of_tendsto_of_frequently (far F Q J Z T ν M g v c q ψ r).norm
    refine (rows ψ support).mono fun s atS=>?_
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by dsimp only [aim,m]; linarith only [atS.1,atS.2])
  have phys:‖grade F Q c (RG17.basket Q 4 (d:=d₄) a r ψ)-pairRead F Q c a r ψ‖≤
      ‖grade F Q c‖*fee F 4*aim:=by
    rw [norm_sub_rev,WilsonCenteredFourOutputSensor.measured,←map_sub]
    have cost:=price ψ support
    norm_num at cost
    exact ((grade F Q c).le_opNorm _).trans ((mul_le_mul_of_nonneg_left cost (norm_nonneg _)).trans_eq
      (by dsimp only [aim,m];ring))
  have total:‖grade F Q c (RG17.basket Q 4 (d:=d₄) a r ψ)-modeled‖≤
      ‖grade F Q c‖*fee F 4*aim+2*aim:=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add phys heard)
  exact total.trans_eq (by dsimp only [aim,m];ring)

end YM.Integration.WilsonCenteredFourOutputReading
