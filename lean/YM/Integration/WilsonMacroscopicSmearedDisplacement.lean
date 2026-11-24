import YM.Integration.WilsonMacroscopicDisplacement

/-! The fixed physical exterior can be a signed smooth detector.  Its price
is the measured absolute unit response on the support of its own test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicSmearedDisplacement
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n}

def read (X : RG17.External R.family V) (r : ℝ) (v : Labels V d) (x : Points n) : ℂ :=
  ∫ z, X.test z * whole V (RG17.posed r x) v (X.offset z) X.labels

def price (X : RG17.External R.family V) : ℝ := ∫ z, ‖X.test z‖*(1+‖X.pay 0 (V.unit 0) z‖)

private theorem price_integrable (F : Spec.Final R.family f V) (X : RG17.External R.family V) :
    Integrable (fun z => ‖X.test z‖*(1+‖X.pay 0 (V.unit 0) z‖)) := by
  have hT : Integrable (fun z=>X.test z) := X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport
  have hP := X.pay_integrable F 0 (V.unit 0)
  apply (hT.norm.add hP.norm).congr
  filter_upwards with z;simp only [Pi.add_apply,norm_mul,mul_add,mul_one]

private theorem held (F : Spec.Final R.family f V) (X : RG17.External R.family V) (r : ℝ) (x : Points n) (v : Labels V d)
    (safe : ∀ z∈tsupport X.test,Injective (beside (RG17.posed r x) (X.offset z))) :
    Integrable (fun z=> X.test z * whole V (RG17.posed r x) v (X.offset z) X.labels) := by
  let h (z : Points (X.n+1)) := X.test z * whole V (RG17.posed r x) v (X.offset z) X.labels
  have inside : tsupport h⊆tsupport X.test := tsupport_mul_subset_left
  have compact : HasCompactSupport h := X.test.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) inside
  apply Continuous.integrable_of_hasCompactSupport _ compact
  apply continuous_of_tsupport;intro z hz
  let loc (q : Points (X.n+1)) : Orbits.Loc (Fin n) (Fin X.n) := (RG17.posed r x,(0:E4),X.offset q)
  have hc : Continuous loc := continuous_const.prodMk (continuous_const.prodMk X.continuous_offset)
  exact X.test.continuous.continuousAt.mul ((Orbits.whole_cont_at v X.labels V F.room.kernel (x:=loc z) (safe z (inside hz))).comp (f:=loc) hc.continuousAt)

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
    (d : Caps n) (X : RG17.External R.family V) {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g) :
    ∃ M a : ℝ,0≤M ∧ 0<a ∧ ∀ᶠ r in RG17.home,∀ x∈K,∀ x'∈K,‖x'-x‖≤a → ∀ v : (i:Fin n)→Free R.family (d i),
      let ins (i : Fin n) := J r (d i) (v i)
      ‖read X r ins x'-read X r ins x‖ ≤ M*price X*(∏ i,‖v i‖)*‖x'-x‖ := by
  obtain ⟨δ,hδ,clear⟩ := X.range_open
  obtain ⟨M,a,hM,ha,bought⟩ := WilsonMacroscopicDisplacement.original hG W source pace hB F fac Q J leading paid d X.labels hk sep hδ hg
  refine ⟨M,a,hM,ha,?_⟩
  have hi := price_integrable F X
  filter_upwards [bought,WilsonMacroscopicDisplacement.joined hk sep hδ (E:=Fin X.n)] with r sl Jn x hx x' hx' small v
  let ins (i : Fin n) := J r (d i) (v i)
  let W (x : Points n) (z : Points (X.n+1)) := whole V (RG17.posed r x) ins (X.offset z) X.labels
  let c := M*(∏ i,‖v i‖)*‖x'-x‖
  have hI (s : Points n) (hs : s∈K) := held F X r s ins (fun z hz=> Jn s hs _ (clear z hz))
  change ‖(∫ z,X.test z * W x' z)-(∫ z,X.test z * W x z)‖ ≤ _
  rw [← integral_sub (hI x' hx') (hI x hx)]
  have dom : ∀ᵐ z, ‖X.test z * W x' z-X.test z * W x z‖ ≤ (‖X.test z‖*(1+‖X.pay 0 (V.unit 0) z‖))*c := by
    filter_upwards with z;by_cases hz:z∈tsupport X.test
    · have q := sl x hx x' small (X.offset z) (clear z hz) none v
      rw [←mul_sub,norm_mul]
      exact (mul_le_mul_of_nonneg_left q (norm_nonneg _)).trans_eq (by dsimp [c,RG17.External.pay,spectator];ring)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  exact (norm_integral_le_of_norm_le (hi.mul_const c) dom).trans_eq (by rw [integral_mul_const];change price X*c=_;dsimp [c];ring)

end YM.Integration.WilsonMacroscopicSmearedDisplacement
