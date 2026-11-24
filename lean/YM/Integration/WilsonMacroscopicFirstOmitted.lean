import YM.Integration.WilsonMacroscopicPointPacket

/-! The first omitted grade as an independently observable signed finite
combination of the genuine macroscopic full-product probes.  This row is
the only remaining contribution at its engineering power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicFirstOmitted
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
open private outer from YM.Integration.WilsonMacroscopicSignedGradient
open private trunc_fields from YM.OPE.Orbits.System
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n}
  (F : Spec.Final R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- A fixed, real-experiment grade reader, calibrated entirely on the
original finite physical external probes. -/
def projected (h : ℕ) : (WilsonMacroscopicDetector.probes F h→ℂ) →L[ℂ] V.Field h :=
  (Q.cutTest h h).toContinuousLinearMap.comp (WilsonMacroscopicDetector.restore F h)

def observed (h : ℕ) (r : ℝ) (x : Points n) (v : Labels V d) : V.Field h :=
  projected F Q h (fun Y=>WilsonMacroscopicSmearedDisplacement.read Y.val r v x)

theorem lower {j h : ℕ} (p : j<h) (v : V.Field j) : projected F Q h (WilsonMacroscopicDetector.read F h (F.sector.derivatives.rise p.le v))=0 := by
  change Q.cutTest h h (WilsonMacroscopicDetector.restore F h (WilsonMacroscopicDetector.read F h _))=0
  rw [WilsonMacroscopicDetector.exact_read,Q.cut_rise,Q.kills_lower h j p]

theorem top (h : ℕ) (v : Q.stratum h) : projected F Q h (WilsonMacroscopicDetector.read F h v.val)=v.val := by
  change Q.cutTest h h (WilsonMacroscopicDetector.restore F h (WilsonMacroscopicDetector.read F h _))=v.val
  rw [WilsonMacroscopicDetector.exact_read];exact Q.test_fixes h v.val v.property

private theorem split_charge (H : ℕ) (x : Fin n→E4) (v : Labels V d) (X : RG17.External R.family V) :
    X.charge F (H+1) (Q.packet (H+1) x v 0) = X.charge F H (Q.packet H x v 0) + X.charge F (H+1) (Q.fresh (H+1) x 0 v) := by
  obtain ⟨δ,hδ,clear⟩ := X.range_open
  change (∫ z,X.test z*X.pay (H+1) _ z)=(∫ z,X.test z*X.pay H _ z)+(∫ z,X.test z*X.pay (H+1) _ z)
  rw [←integral_add (X.pay_integrable F H _) (X.pay_integrable F (H+1) _)]
  apply integral_congr_ae;filter_upwards with z;by_cases hz:z∈tsupport X.test
  · have good := outer hδ (clear z hz)
    have all := packet_read F Q x 0 v (X.offset z) X.labels none (H+1) good
    have previous := packet_read F Q x 0 v (X.offset z) X.labels none H good
    have terms : X.pay (H+1) (Q.packet (H+1) x v 0) z = X.pay H (Q.packet H x v 0) z + X.pay (H+1) (Q.fresh (H+1) x 0 v) z := by
      unfold RG17.External.pay
      change upon (spectator F none) _ _ _ _ _=upon (spectator F none) _ _ _ _ _ + _
      rw [all,previous,trunc_fields,trunc_fields,Fin.sum_univ_castSucc];rfl
    rw [terms,mul_add]
  · simp [image_eq_zero_of_notMem_tsupport hz]

variable {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
  (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
  (fac : OPE.Facilities R.family f V) (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d) (d : Caps n)
  {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)
  (H q : ℕ) {ε : ℝ} (hε : 0<ε)
include hG W source pace hB fac leading paid hk sep hg hε

/-- Real signed detector of the actual first omitted vector at the exact
power `r^(H+1)`, uniformly before the running inputs. -/
theorem fidelity : ∃ C : ℝ,0≤C ∧ ∀ᶠ r in RG17.home,∀ x∈K,∀ v : (i:Fin n)→Free R.family (d i),
    let ins (i : Fin n) := J r (d i) (v i)
    ‖observed F Q (H+1) r x ins-Q.fresh (H+1) (RG17.posed r x) 0 ins‖ ≤ C*(ε*g r^q*r^(H+1)*(∏ i,‖v i‖)) := by
  let h := H+1
  let L := (Q.cutTest h h).toContinuousLinearMap
  have fc : 0≤WilsonMacroscopicDetector.fee F h := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (sum_nonneg fun Y _=>integral_nonneg fun _=>norm_nonneg _)
  refine ⟨‖L‖*WilsonMacroscopicDetector.fee F h,mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) fc,?_⟩
  filter_upwards [WilsonMacroscopicPointPacket.output hG W source pace hB F fac Q J leading paid d hk sep hg h q (σ:=1) one_pos hε] with r bought x hx v
  let ins (i : Fin n) := J r (d i) (v i)
  let recovered := WilsonMacroscopicPointPacket.recovered F h r ins x
  let pack := Q.packet h (RG17.posed r x) ins 0
  have trueRow : L pack=Q.fresh h (RG17.posed r x) 0 ins := Q.filtered_packet h h le_rfl _ ins _
  have test := bought x hx v
  simp only [add_sub_cancel_right,Real.rpow_natCast] at test
  change ‖L recovered-Q.fresh h (RG17.posed r x) 0 ins‖ ≤ _
  rw [←trueRow,←map_sub];exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left test (ContinuousLinearMap.opNorm_nonneg L)).trans_eq (mul_assoc ..).symm)

/-- The true order-H spatial residual minus the *one* first omitted
macroscopic measurement costs every coupling order at its exact integer
engineering power. All uses of the same exterior remain signed. -/
theorem original (X : RG17.External R.family V) : ∃ C : ℝ,0≤C ∧ ∀ᶠ r in RG17.home,∀ x∈K,∀ v : (i:Fin n)→Free R.family (d i),
    let ins (i : Fin n) := J r (d i) (v i)
    let full := WilsonMacroscopicSmearedDisplacement.read X r ins x
    ‖(full-X.charge F H (Q.packet H (RG17.posed r x) ins 0))-X.charge F (H+1) (observed F Q (H+1) r x ins)‖ ≤
      C*(ε*g r^q*r^(H+1)*(∏ i,‖v i‖)) := by
  let L := (X.charge F (H+1)).toContinuousLinearMap
  obtain ⟨B,hB',found⟩ := fidelity F Q hG W source pace hB fac J leading paid d hk sep hg H q hε
  have xn : 0≤WilsonMacroscopicPointPacket.testedMass X := integral_nonneg fun _=>norm_nonneg _
  refine ⟨WilsonMacroscopicPointPacket.testedMass X+‖L‖*B,add_nonneg xn (mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) hB'),?_⟩
  filter_upwards [found,WilsonMacroscopicPointPacket.signed hG W source pace hB F fac Q J leading paid d hk sep hg (H+1) q (σ:=1) one_pos hε X] with r seen late x hx v
  let ins (i : Fin n) := J r (d i) (v i)
  let site := RG17.posed r x
  let full := WilsonMacroscopicSmearedDisplacement.read X r ins x
  let base := X.charge F H (Q.packet H site ins 0)
  let cap := X.charge F (H+1) (Q.packet (H+1) site ins 0)
  let row := Q.fresh (H+1) site 0 ins
  let read := observed F Q (H+1) r x ins
  let cost := ε*g r^q*r^(H+1)*(∏ i,‖v i‖)
  have split : cap=base+L row := split_charge F Q H site ins X
  have all := late x hx v
  simp only [add_sub_cancel_right,Real.rpow_natCast] at all
  have e : ‖L (row-read)‖≤‖L‖*(B*cost) := (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans (seen x hx v)) (ContinuousLinearMap.opNorm_nonneg L))
  change ‖(full-base)-L read‖≤(WilsonMacroscopicPointPacket.testedMass X+‖L‖*B)*cost
  rw [show (full-base)-L read=(full-cap)+L (row-read) by rw [map_sub,split];ring]
  exact (norm_add_le _ _).trans ((add_le_add all e).trans_eq (by ring))

end YM.Integration.WilsonMacroscopicFirstOmitted
