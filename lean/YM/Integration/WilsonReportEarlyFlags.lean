import YM.Integration.WilsonReportPrescribedScene
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! Uniform price of every genuine early marked sector in the physical
running coupling at the prescribed separated positions. The internal
berth resolves an arbitrary prescribed inverse power of the temperature.
Both the entire normalized numerator and the regular product are tested
against the same actual Wilson scene. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportEarlyFlags
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS Trace
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

private theorem shore {n : ℕ} {K : Set (Points n)} (compact : IsCompact K) (inside : K⊆conf n) :
    ∃ t : ℕ,1≤t ∧ ∀ X ∈ K, AtShore t X := by
  have windows : ∀ᶠ j : ℕ in atTop,K⊆Climb.Scaling.window (j:ℝ) n :=
    tendsto_natCast_atTop_atTop.eventually (Work.A05.compact_fits compact inside)
  obtain ⟨t,ht,contained⟩ := ((eventually_ge_atTop 1).and windows).exists
  refine ⟨t,ht,?_⟩
  intro X hX
  obtain ⟨apart,bounded⟩ := contained hX
  refine ⟨fun i=>(PiLp.norm_apply_le X i).trans bounded,?_⟩
  intro i j h
  apply (apart i j h).trans
  unfold cubedist
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  exact fun a=>PiLp.norm_apply_le (X i-X j) a

private theorem shrink (hG : G.Simple) (g : ℝ→ℝ) (hg : Trace.Pilot.Coupling G g)
    (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r in RG17.home,∀ x : ℝ,0≤x → x≤2*g r →
      (8:ℝ)^(q+1)*x^(2*(q+1)) ≤ ε*(g r)^q := by
  let e := q+1
  let A := (8:ℝ)^e*2^(2*e)
  have ap : 0<A := by dsimp [A]; positivity
  have tends := Trace.Pilot.Coupling.conforms hG hg
  filter_upwards [hg.positive,tends.eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1)),
    tends.eventually (gt_mem_nhds (div_pos hε ap))] with r gp small tiny
  intro x hx upper
  have fee : A*g r≤ε := by simpa only [mul_comm] using (lt_div_iff₀ ap).mp tiny |>.le
  calc
    _ ≤ (8:ℝ)^e*(2*g r)^(2*e) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx upper _) (by positivity)
    _ = A*(g r)^(2*e) := by rw [mul_pow]; dsimp only [A]; ring
    _ ≤ A*(g r)^(q+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one gp.le small.le (show q+1≤2*e by dsimp [e]; omega)) ap.le
    _ = (A*g r)*(g r)^q := by rw [pow_succ]; ring
    _ ≤ ε*(g r)^q := mul_le_mul_of_nonneg_right fee (pow_nonneg gp.le _)

/-- After one original finite scene is installed on the preassigned Final,
every finite census, compact separated configuration, true source vector
and desired order receives its presold signed integral error. The exponent
of the internal mesh is independent of the desired error exponent. -/
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
      IsCompact K → K⊆conf _ → ∃ t : ℕ,1≤t ∧ (∀ X∈K,AtShore t X) ∧
    ∀ (o q power : ℕ) (ε : ℝ),0<ε → ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ EnvelopeRange R m k t o r ∧
      ((4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧ (4*n:ℝ)*C.S.a k ≤ r/(t:ℝ)/4) ∧
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J r (d j) (v j)) ∧
      ∀ X∈K,∀ p : ℕ, (∃ x : Fin n→Site (C.side k p),Neighbor R X r ((4*n:ℝ)*C.S.a k) x) ∧
      ∀ N : ℕ,k < N → ∀ x : Fin n→Site (C.side k p),Neighbor R X r (r/(t:ℝ)/4) x →
      ∀ s : Γ.Mode,
      Integrable (gapTag R N s x (shutter R L d r N p w)) (OPE.Therm.scene C.path N p k) ∧
      ‖∫ U,gapTag R N s x (shutter R L d r N p w) U ∂(OPE.Therm.scene C.path N p k)‖≤ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying⟩ :=
    WilsonReportPrescribedScene.selected hG W original subsidy pace hB F fac reader J H paid
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro n Γ d K compact inside
  obtain ⟨t,ht,stays⟩ := shore compact inside
  refine ⟨t,ht,stays,?_⟩
  intro o q power ε hε
  choose e invoices using fun j : Fin n => (paying (d j)).affordability
  let p' := (∑ j,e j)+power
  have flags := scene.allFlags Γ d o t (q+1) p' ht
  have cash := WilsonPhysicalCutoffCurrency.band R hG pace hB g hg
  dsimp only at cash
  rw [←placed] at cash
  filter_upwards [flags,eventually_all.mpr invoices,shrink hG g hg q hε,cash] with r flag representatives cheap band
  dsimp only
  let m := L.level r
  let k := berth R (o+25) m
  obtain ⟨deep,_,envelope,mesh,table⟩ := flag
  refine ⟨deep,envelope,mesh,?_⟩
  intro v hv
  choose w source bound using fun j => (representatives j).1 (v j)
  refine ⟨w,bound,?_⟩
  let β := R.family.path.levels.clock.hatBeta m
  have one : 1≤β := (R.family.path.levels.fits.delayed _).le
  have price (j) : mass R.family (d j) (L.shift (d j) r (w j))≤β^p' := by
    calc
      _ ≤ β^e j*‖v j‖ := source j
      _ ≤ β^e j*β^power := mul_le_mul_of_nonneg_left (hv j) (pow_nonneg (zero_le_one.trans one) _)
      _ = β^(e j+power) := (pow_add ..).symm
      _ ≤ β^p' := pow_le_pow_right₀ one (Nat.add_le_add_right
        (Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)) power)
  intro X hX p
  obtain ⟨sample,invoice⟩ := table X (stays X hX) p
  refine ⟨sample,?_⟩
  intro N step x neighbor s
  obtain ⟨integrable,limit⟩ := invoice N step w price x neighbor s
  have visible : m≤N := (deep.trans step).le
  exact ⟨integrable,limit.trans (cheap _ (RG16.Literal.g_pos R.makes visible).le (band N p visible).2)⟩

end YM.Integration.WilsonReportEarlyFlags
end

