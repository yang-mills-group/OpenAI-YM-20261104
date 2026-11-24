import YM.Integration.WilsonMacroscopicSignedGradient
import YM.Integration.WilsonMacroscopicSmearedDisplacement
import YM.Integration.WilsonMacroscopicDetector

/-! Positive-horizon extraction from the fixed macroscopic signed physical
observations at the actual inner points, before choosing the running inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicPointPacket
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
open private held from YM.Integration.WilsonMacroscopicSmearedDisplacement
open private outer from YM.Integration.WilsonMacroscopicSignedGradient
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n}

def testedMass (X : RG17.External R.family V) : ℝ := ∫ z, ‖X.test z‖

def recovered (F : Spec.Final R.family f V) (H : ℕ) (r : ℝ) (v : Labels V d) (x : Points n) : V.Field H :=
  WilsonMacroscopicDetector.restore F H (fun X : WilsonMacroscopicDetector.probes F H=>WilsonMacroscopicSmearedDisplacement.read X.val r v x)

/-- This numerical difference contains only genuine full-product measurements
and the fixed physical calibration; it contains no coefficients from `Q`. -/
def erased (F : Spec.Final R.family f V) (H : ℕ) (X : RG17.External R.family V) (r : ℝ) (v : Labels V d) (x : Points n) : ℂ :=
  WilsonMacroscopicSmearedDisplacement.read X r v x - X.charge F H (recovered F H r v x)

variable {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
  (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
  (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d) (d : Caps n)
  {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)
  (H q : ℕ) {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε)
include hG W source pace hB fac leading paid hk sep hg hσ hε

theorem signed (X : RG17.External R.family V) : ∀ᶠ r in RG17.home,∀ x∈K,∀ v : (i:Fin n)→Free R.family (d i),
    let ins (i : Fin n) := J r (d i) (v i)
    ‖WilsonMacroscopicSmearedDisplacement.read X r ins x - X.charge F H (Q.packet H (RG17.posed r x) ins 0)‖ ≤
      testedMass X * (ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)) := by
  obtain ⟨δ,hδ,clear⟩ := X.range_open
  have purchased := WilsonMacroscopicUniformRemainder.original hG W source pace hB F fac Q J leading paid d X.labels hk sep hδ hg H q hσ hε
  filter_upwards [purchased,WilsonMacroscopicDisplacement.joined hk sep hδ (E:=Fin X.n)] with r priced joins x hx v
  let ins (i : Fin n) := J r (d i) (v i)
  let pack := Q.packet H (RG17.posed r x) ins 0
  let c := ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)
  let full (z : Points (X.n+1)) := whole V (RG17.posed r x) ins (X.offset z) X.labels
  have hI := held F X r x ins (fun z hz=>joins x hx _ (clear z hz))
  have hi : Integrable (fun z=>X.test z) := X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport
  change ‖(∫ z,X.test z*full z) - (∫ z,X.test z*X.pay H pack z)‖ ≤ testedMass X*c
  rw [←integral_sub hI (X.pay_integrable F H pack)]
  have dom : ∀ᵐ z,‖X.test z*full z-X.test z*X.pay H pack z‖ ≤ ‖X.test z‖*c := by
    filter_upwards with z;by_cases hz:z∈tsupport X.test
    · have paid := priced x hx (X.offset z) (clear z hz) none v
      have reading := packet_read F Q (RG17.posed r x) 0 ins (X.offset z) X.labels none H (outer hδ (clear z hz))
      change ‖full z-trunc V F Q H (RG17.posed r x) 0 ins (X.offset z) X.labels‖≤c at paid
      change X.pay H pack z=trunc V F Q H (RG17.posed r x) 0 ins (X.offset z) X.labels at reading
      rw [←mul_sub,norm_mul,reading];exact mul_le_mul_of_nonneg_left paid (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  exact (norm_integral_le_of_norm_le (hi.norm.mul_const c) dom).trans_eq (integral_mul_const ..)

theorem output : ∀ᶠ r in RG17.home,∀ x∈K,∀ v : (i:Fin n)→Free R.family (d i),
    let ins (i : Fin n) := J r (d i) (v i)
    ‖recovered F H r ins x - Q.packet H (RG17.posed r x) ins 0‖ ≤
      WilsonMacroscopicDetector.fee F H*(ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)) := by
  let Z := WilsonMacroscopicDetector.probes F H
  have all := eventually_all.mpr fun Y : Z => signed hG W source pace hB F fac Q J leading paid d hk sep hg H q hσ hε Y.val
  filter_upwards [all,RG17.positiveLength,hg.positive] with r buy rp gp x hx v
  let ins (i : Fin n) := J r (d i) (v i)
  let pack := Q.packet H (RG17.posed r x) ins 0
  let xs (Y : Z) := WilsonMacroscopicSmearedDisplacement.read Y.val r ins x
  let c := ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)
  have cp : 0≤c := mul_nonneg (mul_nonneg (mul_nonneg hε.le (pow_nonneg gp.le _)) (Real.rpow_nonneg rp.le _)) (prod_nonneg fun _ _=>norm_nonneg _)
  have xp (Y : Z) : 0≤testedMass Y.val := integral_nonneg fun _=>norm_nonneg _
  have price : ‖xs-WilsonMacroscopicDetector.read F H pack‖≤(∑ Y : Z,testedMass Y.val)*c := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (sum_nonneg fun Y _=>xp Y) cp)).mpr
    intro Y
    exact (buy Y x hx v).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun Y _=>xp Y) (mem_univ Y)) cp)
  have eq : recovered F H r ins x-pack=WilsonMacroscopicDetector.restore F H (xs-WilsonMacroscopicDetector.read F H pack) := by rw [map_sub,WilsonMacroscopicDetector.exact_read];rfl
  change ‖recovered F H r ins x-pack‖≤WilsonMacroscopicDetector.fee F H*c
  rw [eq];exact ((WilsonMacroscopicDetector.restore F H).le_opNorm _).trans ((mul_le_mul_of_nonneg_left price (norm_nonneg _)).trans_eq (mul_assoc ..).symm)

include Q in
theorem residual (X : RG17.External R.family V) : ∃ C : ℝ,0≤C ∧ ∀ᶠ r in RG17.home,∀ x∈K,∀ v : (i:Fin n)→Free R.family (d i),
    let ins (i : Fin n) := J r (d i) (v i)
    ‖erased F H X r ins x‖ ≤ C*(ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)) := by
  let L := (X.charge F H).toContinuousLinearMap
  have xp : 0≤testedMass X := integral_nonneg fun _=>norm_nonneg _
  have fc : 0≤WilsonMacroscopicDetector.fee F H := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (sum_nonneg fun Y _=>integral_nonneg fun _=>norm_nonneg _)
  refine ⟨testedMass X+‖L‖*WilsonMacroscopicDetector.fee F H,add_nonneg xp (mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) fc),?_⟩
  filter_upwards [signed hG W source pace hB F fac Q J leading paid d hk sep hg H q hσ hε X,output hG W source pace hB F fac Q J leading paid d hk sep hg H q hσ hε] with r seen restored x hx v
  let ins (i : Fin n) := J r (d i) (v i)
  let p := Q.packet H (RG17.posed r x) ins 0
  let u := WilsonMacroscopicSmearedDisplacement.read X r ins x
  let emitted := recovered F H r ins x
  let c := ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖)
  have e : ‖L p-L emitted‖≤‖L‖*(WilsonMacroscopicDetector.fee F H*c) := by
    rw [←map_sub];exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans (restored x hx v)) (norm_nonneg _))
  change ‖u-L emitted‖≤(testedMass X+‖L‖*WilsonMacroscopicDetector.fee F H)*c
  exact (norm_sub_le_norm_sub_add_norm_sub u (L p) (L emitted)).trans ((add_le_add (seen x hx v) e).trans_eq (by ring))

end YM.Integration.WilsonMacroscopicPointPacket
