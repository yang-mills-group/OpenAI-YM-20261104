import YM.Integration.WilsonReportWindowRead
import YM.Integration.WilsonReportUnmaskedConnected
import YM.Integration.WilsonReportFittedCurrency

/-! The actual numerical connected and unconnected pre-report in the physical
fitted coordinates, after the complete signed prior-failure correction has
been paid on the original Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFittedPositions
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Cells OPE.Strobe.Panoramic Push.GridApprox WilsonReportColumnCut
open Extra.Trajectories (connected)
open Next.Rank.Spindle WilsonReportWindowSource Pert.Asymptotics
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportMomentDifference
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- All funders, including the fine history and the compartment for each
continuum label, can be held fixed before requesting the physical window read. -/
theorem on_scene (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) {F : Spec.Final R.family f S} (services : OPE.Services R.family f S)
    (J : ℝ→PhysMS.tower S) {u₀ : Filter UVIndex} {Q : Lenses.Mantle F u₀} (L : Layout F)
    (pegs : Pegs Q L) (placed : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (scene : Pier.Scene.ScenePlan R F L) (paying : ∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d)
    (g : ℝ→ℝ) (hg : Trace.Pilot.Coupling G g)
    {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) {K : Set (Points n)} {t : ℕ} (ht : 1≤t)
    (stays : ∀ X∈K,AtShore t X) :
    ∀ (o q power : ℕ) (ε : ℝ),0<ε → ∃ signedCost : ℕ, ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ EnvelopeRange R m k t o r ∧
      ((4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧ (4*n:ℝ)*C.S.a k ≤ r/(t:ℝ)/4) ∧
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J r (d j) (v j)) ∧
      (∀ j,mass C (d j) (L.shift (d j) r (w j))≤C.path.levels.clock.hatBeta m^signedCost) ∧
      ∀ X∈K,∀ p : ℕ, (∃ x : Fin n→Site (C.side k p),Neighbor R X r ((4*n:ℝ)*C.S.a k) x) ∧
      ∀ N : ℕ,∀ cut : k < N,∀ x : Fin n→Site (C.side k p),Neighbor R X r (r/(t:ℝ)/4) x →
      let B := (C.path.levels.budget k).B
      let localField (j : Fin n) := opened C (N:=N) (atRef L (d j) r (N,p) (w j)) (x j)
      (∀ j,Interior (window (x j) (omen C (d j) k B)) (localized L r (d j) k N p (w j) (x j))) ∧
      (∀ i j : Fin n,i≠j→Disjoint (window (x i) (omen C (d i) k B)) (window (x j) (omen C (d j) k B))) ∧
      (∀ A : Finset (Fin n), ‖moment (C.beta N p) (fun U=>∏j∈A,fine L d w r cut.le x j U)-
        ∫U,∏j∈A,localField j U ∂(Therm.scene C.path N p k)‖≤ε*(g r)^q) ∧
      ∀ s : Γ.Mode,
      ‖(connected (microscopic Γ C (fine L d w r cut.le x))).part s -
        (connected (reported Γ C (N:=N) localField)).part s‖ ≤ ε*(g r)^q := by
  intro o q power ε hε
  let half := ε/2
  have hp : 0<half := half_pos hε
  obtain ⟨h,read⟩ := WilsonReportWindowRead.on_scene hG W original subsidy pace hB services J L pegs placed scene
    paying g hg Γ d ht stays o q power half hp
  let a := (o+27)*((∑j,d j)+1)+h
  let D := n+1+n*Fintype.card (Hot Γ)
  let q' := q+2*(a*D)
  let price := WilsonReportFittedCurrency.factor n a D q
  have price₀ : 0<price := by dsimp only [price,WilsonReportFittedCurrency.factor]; positivity
  let e := half/price
  have ep : 0<e := div_pos hp price₀
  have exactCost : e*price=half := div_mul_cancel₀ _ price₀.ne'
  have raw := WilsonReportUnmaskedMoments.physical hG W original subsidy d q' ep
  have joined := WilsonReportUnmaskedConnected.physical hG W original subsidy Γ d q' ep
  obtain ⟨bound,qualify⟩ := eventually_atTop.1 (raw.and joined)
  have grades := eventually_all.mpr fun j : Fin n=>pegs.level.growing.eventually_ge_atTop (R.family.ref (d j))
  have temp := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  rw [←placed] at temp
  have warm := temp.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  refine ⟨h,?_⟩
  filter_upwards [read,pegs.level.growing.eventually_ge_atTop bound,grades,warm,hg.positive] with
    r report paid grade fit gp
  dsimp only at report ⊢
  obtain ⟨deep,E,mesh,voters⟩ := report
  let m := L.level r
  let k := berth R (o+25) m
  let C := R.family
  refine ⟨deep,E,mesh,?_⟩
  intro v hv
  obtain ⟨w,agrees,budget,next⟩ := voters v hv
  refine ⟨w,agrees,budget,?_⟩
  intro X hX p
  obtain ⟨sample,working⟩ := next X hX p
  refine ⟨sample,?_⟩
  intro N cut x neighbor
  let V (j : Fin n) := atRef L (d j) r (N,p) (w j)
  let C₀ (j : Fin n) := localized L r (d j) k N p (w j) (x j)
  let C₁ (j : Fin n) := opened C (N:=N) (V j) (x j)
  let z := regulatorRun C N p k
  let A := 1+∑j,Spindle.paid C (d j) k N p (V j)
  have A1 : 1≤A := le_add_of_nonneg_right (sum_nonneg (fun j _=>Spindle.paid_pos C (d j) k N p (V j)))
  have zp : 0<z := RG16.Literal.g_pos R.makes cut.le
  have billed := WilsonReportFittedCurrency.at_fields (p:=p) hG L services d w gp fit.le deep.le cut.le grade E.zoom budget D q
  have pricePaid : e*A^D*z^q'≤half*(g r)^q :=
    (mul_assoc e (A^D) (z^q')).le.trans ((mul_le_mul_of_nonneg_left billed ep.le).trans_eq
      ((mul_assoc e price ((g r)^q)).symm.trans (congrArg (· * (g r)^q) exactCost)))
  have act := qualify k (paid.trans deep.le)
  obtain ⟨support,apart,raw₀,joined₀⟩ := working N cut x neighbor
  refine ⟨support,apart,?_,?_⟩
  · intro I
    have localBill := act.1 N p cut V x I
    have relative : e*A^(n+1)*z^q'≤half*(g r)^q := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ A1 (Nat.le_add_right (n+1) (n*Fintype.card (Hot Γ)))) ep.le)
      (pow_nonneg zp.le _)).trans pricePaid
    have right := localBill.trans relative
    apply (norm_sub_le_norm_sub_add_norm_sub _ (∫U,∏j∈I,C₀ j U ∂Therm.scene C.path N p k) _).trans
    exact (add_le_add (raw₀ I) right).trans_eq (by dsimp only [half]; ring)
  intro s
  have right := (act.2 N p cut V x s).trans pricePaid
  apply (norm_sub_le_norm_sub_add_norm_sub _ ((connected (reported Γ C (N:=N) C₀)).part s) _).trans
  exact (add_le_add (joined₀ s) right).trans_eq (by dsimp only [half]; ring)

/-- The two connected fields are computed by the original Möbius inverse
of the complete finite moment tables on their respective genuine laws.
The same output labels work simultaneously for every mode, position,
admissible grid representative, cutoff, and period. -/
theorem on_run (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
    (g : ℝ→ℝ) (hg : Trace.Pilot.Coupling G g) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
    ∀ {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ) {K : Set (Points n)},
      IsCompact K → K⊆conf _ → ∃ t : ℕ,1≤t ∧ (∀ X∈K, AtShore t X) ∧
    ∀ (o q power : ℕ) (ε : ℝ),0<ε → ∃ signedCost : ℕ, ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ EnvelopeRange R m k t o r ∧
      ((4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧ (4*n:ℝ)*C.S.a k ≤ r/(t:ℝ)/4) ∧
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J r (d j) (v j)) ∧
      (∀ j,mass C (d j) (L.shift (d j) r (w j))≤C.path.levels.clock.hatBeta m^signedCost) ∧
      ∀ X∈K,∀ p : ℕ, (∃ x : Fin n→Site (C.side k p),Neighbor R X r ((4*n:ℝ)*C.S.a k) x) ∧
      ∀ N : ℕ,∀ cut : k < N,∀ x : Fin n→Site (C.side k p),Neighbor R X r (r/(t:ℝ)/4) x →
      let B := (C.path.levels.budget k).B
      let localField (j : Fin n) := opened C (N:=N) (atRef L (d j) r (N,p) (w j)) (x j)
      (∀ j,Interior (window (x j) (omen C (d j) k B)) (localized L r (d j) k N p (w j) (x j))) ∧
      (∀ i j : Fin n,i≠j→Disjoint (window (x i) (omen C (d i) k B)) (window (x j) (omen C (d j) k B))) ∧
      (∀ A : Finset (Fin n), ‖moment (C.beta N p) (fun U=>∏j∈A,fine L d w r cut.le x j U)-
        ∫U,∏j∈A,localField j U ∂(Therm.scene C.path N p k)‖≤ε*(g r)^q) ∧
      ∀ s : Γ.Mode,
      ‖(connected (microscopic Γ C (fine L d w r cut.le x))).part s -
        (connected (reported Γ C (N:=N) localField)).part s‖ ≤ ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,early⟩ :=
    WilsonReportEarlyFlags.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro n Γ d K compact inside
  obtain ⟨t,ht,stays,_⟩ := early Γ d compact inside
  exact ⟨t,ht,stays,on_scene hG W original subsidy pace hB fac.toServices J L pegs placed scene paying
    g hg Γ d ht stays⟩

end YM.Integration.WilsonReportFittedPositions
end

