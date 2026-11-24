import Batteries.Tactic.OpenPrivate
import YM.Integration.WilsonMacroscopicDisplacement
import YM.Integration.WilsonMacroscopicUniformRemainder

/-! A derivative of the original physical correlation with its actual
through-horizon field response subtracted. This is the signed price that
survives a subsequent positive-degree extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicSignedGradient
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
open private higher replacement price funded from YM.Integration.WilsonMacroscopicDerivativePrice
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n} {E : Type} [Fintype E] {e : E→ℕ}

/-- The original reader's complete promoted packet, independent of the
macroscopic tester.  The normalized field in the promoted slot represents
the actual `r D_a(J(r)v)` and has the uniform measured descendant price. -/
def packet (F : Spec.Final R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower V) (H : ℕ) (i : Fin n) (a : Axis) (r : ℝ) (x : Points n) (v : (j:Fin n)→Free R.family (d j)) : V.Field H :=
  let D := F.sector.derivatives.deriv (d i) a (J r (d i) (v i))
  let z := (J r (d i+1)).symm ((r:ℂ) • D)
  Q.packet H (RG17.posed r x) (fun j=>J r (higher d i j) (replacement v i z j)) 0

private theorem outer {δ : ℝ} (hδ : 0<δ) {y : E→E4} (h : ClearOf 0 y δ) : Injective (beside (sole (0:E4)) y) := by
  refine beside_distinct.mpr ⟨fun _ _ _=>Subsingleton.elim _ _,?_,?_⟩
  · intro j k eq;by_contra ne;have q := h.spread j k ne
    rw [eq,sub_self,norm_zero] at q;exact (not_le_of_gt hδ) q
  · intro _ j eq;have q := h.openSpace j
    change (0:E4)=y j at eq
    rw [←eq,sub_self,norm_zero] at q;exact (not_le_of_gt hδ) q

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d) (d : Caps n) (i : Fin n) (a : Axis) (w : Labels V e)
    {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {δ : ℝ} (hδ : 0<δ) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)
    (H q : ℕ) {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∀ᶠ r in RG17.home,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ → ∀ t : Viewers F,∀ v : (j:Fin n)→Free R.family (d j),
      let read (s : Points n) := whole (spectator F t) (RG17.posed r s) (fun j=>J r (d j) (v j)) y w
      ‖Points.gradient i a read x - upon (spectator F t) H 0 y w (packet F Q J H i a r x v)‖ ≤
        ε*g r^q*r^((H:ℝ)+1-σ)*(∏ j,‖v j‖) := by
  have available := WilsonReportPrescribedFrame.present F J leading paid
  obtain ⟨c,hc,column⟩ := WilsonMacroscopicDescendant.paid F J available (d i) a
  have positive : 0<c+1 := by linarith only [hc]
  have bought := WilsonMacroscopicUniformRemainder.original hG W source pace hB F fac Q J leading paid (higher d i) w hk sep hδ hg H q hσ (div_pos hε positive)
  filter_upwards [bought,column,WilsonMacroscopicDisplacement.joined hk sep hδ (E:=E),RG17.positiveLength,hg.positive] with r bill charge joins rp gp x hx y clear t v
  let ins (j : Fin n) := J r (d j) (v j)
  let D := F.sector.derivatives.deriv (d i) a (ins i)
  let z := (J r (d i+1)).symm ((r:ℂ) • D)
  let inputs (j : Fin n) := J r (higher d i j) (replacement v i z j)
  let Cμ := g r^q*r^((H:ℝ)+1-σ)
  have CN : 0≤Cμ := mul_nonneg (pow_nonneg gp.le _) (Real.rpow_nonneg rp.le _)
  have vv : 0 ≤ ∏ j,‖v j‖ := prod_nonneg fun _ _=>norm_nonneg _
  have receipt := bill x hx y clear t (replacement v i z)
  have exactReading := packet_read F Q (RG17.posed r x) 0 inputs y w t H (outer hδ clear)
  have identity := WilsonMacroscopicRelativeGradient.at_slot F t (fun j=> (⟨d j,ins j⟩ : V.Tag)) (fun j=> (⟨e j,w j⟩ : V.Tag)) r y (joins x hx y clear) i a
  change Points.gradient i a (fun s : Points n=>whole (spectator F t) (RG17.posed r s) ins y w) x =
    r • whole (spectator F t) (RG17.posed r x) (voices (update (fun j=> (⟨d j,ins j⟩ : V.Tag)) i ⟨d i+1,D⟩)) y w at identity
  change ‖Points.gradient i a (fun s : Points n=>whole (spectator F t) (RG17.posed r s) ins y w) x - upon (spectator F t) H 0 y w (Q.packet H (RG17.posed r x) inputs 0)‖ ≤ _
  rw [identity,funded F J r v i a (RG17.posed r x) y w t,exactReading]
  have cp : (ε/(c+1))*c≤ε := by rw [div_mul_eq_mul_div,div_le_iff₀ positive];nlinarith only [hε]
  refine receipt.trans ?_
  calc
    _ ≤ (ε/(c+1))*g r^q*r^((H:ℝ)+1-σ)*(c*∏ j,‖v j‖) := mul_le_mul_of_nonneg_left (price v i (charge (v i))) (mul_nonneg (mul_nonneg (div_nonneg hε.le positive.le) (pow_nonneg gp.le _)) (Real.rpow_nonneg rp.le _))
    _ = ((ε/(c+1))*c)*Cμ*(∏ j,‖v j‖) := by dsimp [Cμ];ring
    _ ≤ ε*Cμ*(∏ j,‖v j‖) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cp CN) vv
    _ = _ := by dsimp [Cμ];ring

end YM.Integration.WilsonMacroscopicSignedGradient
