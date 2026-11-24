import YM.Integration.WilsonMacroscopicPrescribedInputs
import YM.OPE.Short.Vacuum

/-! A bounded near moment controls the true leading channel even when the
other fields are held at a fixed physical distance. Both physical tests
use the same intrinsic packet and the same prescribed running input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicVacuumFactor
open Function Filter Finset Set MeasureTheory Extraction Table
open Spec Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
variable {I E : Type} [Fintype I] [Fintype E] {d : I→ℕ} {e : E→ℕ}

theorem grade_zero (F : Spec.Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (x : I→E4) (o : E4) (v : Labels V d) (y : E→E4) (w : Labels V e) (t : Viewers F) :
    formula F Q x o v y w 0 t = whole (spectator F t) x v y w -
      upon (spectator F t) 0 o y w (Q.fresh 0 x o v) := by
  change whole (spectator F t) x v y w - trunc (spectator F t) F Q 0 x o v y w = _
  rw [←tested_fields]
  simp [balance];rfl

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
    {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
    (v : (i:I)→RG17.Free R.family (d i)) (w : Labels V e) {M η δ : ℝ} (hM : 0≤M) (hη : 0<η) (hδ : 0<δ)
    {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g) (p : ℕ) {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ (x : I→E4) (o : E4) (y : E→E4),
      WithinRoom r M η x o → Injective x → ClearOf o y δ → ∀ t : Viewers F,
        let ins : Labels V d := fun i=>J r (d i) (v i)
        let ext := upon (spectator F t) 0 o y w (V.unit 0)
        ‖whole (spectator F t) x ins y w - Orbits.moment V x ins * ext‖ ≤
          ε*g r^p*r^(1-σ)*(1+‖ext‖) := by
  let base (z : Empty) : V.Tag := OPE.Short.extra (z:=z)
  let ghosts := voices base
  have full := WilsonMacroscopicPrescribedInputs.original hG W source pace hB F fac Q J leading paid d v w hM hη hδ hg 0 p hσ hε
  have near := WilsonMacroscopicPrescribedInputs.original hG W source pace hB F fac Q J leading paid d v ghosts hM hη hδ hg 0 p hσ hε
  filter_upwards [full,near] with r compares receipt x o y fits injective clear t
  let ins : Labels V d := fun i=>J r (d i) (v i)
  let word (i : I) : V.Tag := ⟨d i,ins i⟩
  let ext := upon (spectator F t) 0 o y w (V.unit 0)
  let bill := ε*g r^p*r^(1-σ)
  obtain ⟨z,zEq⟩ := RG12.Kintsugi.Spot.unit_desc (C:=R.family) (S:=V) hG (by norm_num : (0:ℕ)<4) (Q.fresh 0 x o ins)
  have both := compares x o y fits clear t
  simp only [Nat.cast_zero,zero_add] at both
  change ‖formula F Q x o ins y w 0 t‖≤bill at both
  rw [grade_zero,zEq,map_smul] at both
  have other := receipt x o OPE.Short.gapPos fits (by constructor <;> intro z <;> cases z) none
  simp only [Nat.cast_zero,zero_add] at other
  change ‖formula F Q x o ins OPE.Short.gapPos ghosts 0 none‖≤bill at other
  rw [grade_zero,zEq,map_smul] at other
  have obs : whole V x ins OPE.Short.gapPos ghosts = Orbits.moment V x ins := OPE.Short.tagged F word x none injective
  change ‖whole V x ins OPE.Short.gapPos ghosts-z*(upon V 0 o OPE.Short.gapPos ghosts (V.unit 0))‖≤bill at other
  rw [obs,show upon V 0 o OPE.Short.gapPos ghosts (V.unit 0)=1 from OPE.Short.vacuum F none o _ base,mul_one] at other
  change ‖whole (spectator F t) x ins y w-Orbits.moment V x ins*ext‖≤bill*(1+‖ext‖)
  calc
    _ ≤ ‖whole (spectator F t) x ins y w-z*ext‖ + ‖z*ext-Orbits.moment V x ins*ext‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ bill + bill*‖ext‖ := add_le_add both (by rw [←sub_mul,norm_mul,norm_sub_rev]; exact mul_le_mul_of_nonneg_right other (norm_nonneg _))
    _ = _ := by ring

end YM.Integration.WilsonMacroscopicVacuumFactor
