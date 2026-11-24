import YM.Integration.WilsonReportRegularMoments
import YM.Integration.WilsonReportConnectedCurrency

/-! Full mixed connected early-report remainder on the physical Wilson history
at the independently prescribed continuum fields. Every disconnected partition
partner is the signed original microscopic or genuine regular coarse moment.
The estimate is uniform before all periods and cutoffs on compact separated
positions, at the source's arbitrarily fine internal berth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportEarlyConnected
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportMomentDifference
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

private theorem single {b a x : ℝ} (hb : 3≤b) (ha : 0≤a) (h : a≤2*b) {j w t : ℕ} (hj : j≤w)
    (hx : x≤b^t) : 3*(a^j*x) ≤ b^(1+2*w+t) := by
  have b1 : 1≤b := by linarith only [hb]
  have b0 := zero_le_one.trans b1
  have aa : a≤b^2 := h.trans (by nlinarith only [mul_le_mul_of_nonneg_right hb b0])
  have left : a^j ≤ b^(2*w) := (pow_le_pow_left₀ ha aa _).trans
    ((pow_le_pow_right₀ (one_le_pow₀ b1) hj).trans_eq (pow_mul b 2 w).symm)
  calc
    _ ≤ 3*(b^(2*w)*b^t) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (pow_nonneg ha _)) (by norm_num) |>.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right left (pow_nonneg b0 _)) (by norm_num))
    _ ≤ b*(b^(2*w)*b^t) := mul_le_mul_of_nonneg_right hb (mul_nonneg (pow_nonneg b0 _) (pow_nonneg b0 _))
    _ = _ := by rw [pow_add,pow_add,pow_one]; ring

private theorem products {b : ℝ} (hb : 2≤b) (a n h : ℕ) :
    (1+(b^a)^n)^h ≤ b^((a*n+1)*h) := by
  have b1 : 1≤b := by linarith only [hb]
  have b0 := zero_le_one.trans b1
  have one := one_le_pow₀ (n:=a*n) b1
  have room : 1+b^(a*n) ≤ b^(a*n+1) := calc
    _ ≤ b^(a*n)*2 := by linarith
    _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_left hb (pow_nonneg b0 _)
  rw [←pow_mul,pow_mul b (a*n+1) h]
  exact pow_le_pow_left₀ (by positivity) room h

private theorem multiple {n : ℕ} (Γ : Census (Fin n)) (s : Γ.Mode) :
    0 ≤ WilsonReportMomentDifference.multiplicity Γ s := by
  unfold WilsonReportMomentDifference.multiplicity
  exact sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

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
    ∀ (o q power : ℕ) (ε : ℝ),0<ε → ∀ᶠ r in RG17.home,
      let C := R.family; let m := L.level r; let k := berth R (o+25) m
      m < k ∧ EnvelopeRange R m k t o r ∧
      ((4*n:ℝ)*C.S.a k ≤ r/C.path.levels.clock.hatBeta m^o ∧ (4*n:ℝ)*C.S.a k ≤ r/(t:ℝ)/4) ∧
      ∀ v : (j:Fin n)→RG17.Free C (d j),(∀ j,‖v j‖≤C.path.levels.clock.hatBeta m^power) →
      ∃ w : (j:Fin n)→C.label (d j),(∀ j,master L (d j) r (w j)=J r (d j) (v j)) ∧
      ∀ X∈K,∀ p : ℕ, (∃ x : Fin n→Site (C.side k p),Neighbor R X r ((4*n:ℝ)*C.S.a k) x) ∧
      ∀ N : ℕ,∀ cut : k < N,∀ x : Fin n→Site (C.side k p),Neighbor R X r (r/(t:ℝ)/4) x →
      ∀ s : Γ.Mode,
      ‖(connected (microscopic Γ C (fine L d w r cut.le x))).part s -
        (connected (reported Γ C (N:=N) (coarse L d w r (N:=N) x))).part s‖ ≤ ε*(g r)^q := by
  obtain ⟨u,Q,L,hu,pegs,placed,scene,paying,early⟩ :=
    WilsonReportEarlyFlags.on_run hG W original subsidy pace hB F fac reader J H paid g hg
  refine ⟨u,Q,L,hu,pegs,placed,scene,paying,?_⟩
  intro n Γ d K compact inside
  obtain ⟨t,ht,stays,_⟩ := early Γ d compact inside
  refine ⟨t,ht,stays,?_⟩
  intro o q power ε hε
  let Ω : Census (Fin n) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  choose e invoices using fun j : Fin n => (paying (d j)).affordability
  let labels := (∑ j,e j)+power
  let order := 1+(o+27)*((∑ j,d j)+1)
  let a := 1+2*order+labels
  let D := (a*n+1)*Fintype.card (Hot Γ)
  let E := q+D+1
  let c := 1+∑ s : Γ.Mode,WilsonReportMomentDifference.multiplicity Γ s
  have cpos : 0<c := by
    dsimp only [c]
    linarith only [sum_nonneg (s:=univ) (fun (s : Γ.Mode) _=>multiple Γ s)]
  have fees := WilsonReportConnectedCurrency.absorb R hG pace hB g hg D q cpos hε
  dsimp only at fees
  rw [←placed] at fees
  have flags := scene.allFlags Ω d o t E labels ht
  have grades := eventually_all.mpr fun j : Fin n=>pegs.level.growing.eventually_ge_atTop (R.family.ref (d j))
  have zero := pegs.level.growing.eventually_ge_atTop (R.family.ref 0)
  have warmth := ((Next.Rank.Station.hat_rate R.family.path.levels hG).comp pegs.level.growing).eventually_ge_atTop (3:ℝ)
  filter_upwards [flags,eventually_all.mpr invoices,fees,grades,zero,warmth] with r flag reps tariff grade g0 hot
  let m := L.level r
  let k := berth R (o+25) m
  let b := R.family.path.levels.clock.hatBeta m
  have b1 : 1≤b := (R.family.path.levels.fits.delayed m).le
  have b0 := zero_le_one.trans b1
  dsimp only
  obtain ⟨deep,_,cover,mesh,table⟩ := flag
  refine ⟨deep,cover,mesh,?_⟩
  intro v hv
  choose w cost agrees using fun j=>(reps j).1 (v j)
  refine ⟨w,agrees,?_⟩
  have budget (j) : mass R.family (d j) (L.shift (d j) r (w j))≤b^labels := by
    calc
      _ ≤ b^e j*‖v j‖ := cost j
      _ ≤ b^e j*b^power := mul_le_mul_of_nonneg_left (hv j) (pow_nonneg b0 _)
      _ = b^(e j+power) := (pow_add ..).symm
      _ ≤ b^labels := pow_le_pow_right₀ b1 (Nat.add_le_add_right
        (Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (mem_univ j)) power)
  intro X hX p
  obtain ⟨sample,earlier⟩ := table X (stays X hX) p
  refine ⟨sample,?_⟩
  intro N cut x neighbor s
  let FF := fine L d w r cut.le x
  let SS := coarse L d w r (N:=N) x
  let z := Pert.Asymptotics.regulatorRun R.family N p m
  let h := (8:ℝ)^E*z^(2*E)
  have hp : 0≤h := mul_nonneg (by positivity) (pow_nonneg (RG16.Literal.g_pos R.makes (deep.trans cut).le).le _)
  have unit := tariff N p (deep.trans cut).le
  have physical (A : Finset (Fin n)) : ‖moment (R.family.beta N p) (fun U=>∏ j∈A,FF j U) -
      (∫ U,∏ j∈A,SS j U ∂OPE.Therm.scene R.family.path N p k)‖ ≤ h := by
    let u : Ω.Mode := ⟨A,mem_univ _⟩
    obtain ⟨live,bill⟩ := earlier N cut w budget x neighbor u
    have exactJoint := (WilsonReportRegularMoments.identity L d w r cut.le x u live).2
    exact (congrArg norm exactJoint).le.trans bill
  have bounded (j : Fin n) (U) : ‖SS j U‖ ≤ b^a := by
    have price := WilsonReportRegularMoments.regular hG W original subsidy L fac.toServices r (w j)
      (grade j) (g0.trans_lt deep) deep.le cut cover.zoom (x j) U
    have jd : d j ≤ ∑ i,d i := single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (mem_univ j)
    have orderBound : 1+(o+27)*(d j+1)≤order := Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right jd _)) _
    exact price.trans (single hot (zero_le_one.trans (R.family.path.levels.fits.delayed k).le)
      cover.compat orderBound (budget j))
  have exactConnected := WilsonReportMomentDifference.original Γ R.family R.makes cut.le FF SS hp unit.1
    (one_le_pow₀ b1) bounded physical s
  have mult : WilsonReportMomentDifference.multiplicity Γ s≤c := by
    dsimp only [c]
    have all := single_le_sum (f:=WilsonReportMomentDifference.multiplicity Γ) (fun j _=>multiple Γ j) (mem_univ s)
    linarith only [all]
  have hot' : 2≤b := (show (2:ℝ)≤3 by norm_num).trans hot
  have polynomial : (1+(b^a)^Fintype.card (Fin n))^Fintype.card (Hot Γ)≤b^D := by
    simpa only [D,Fintype.card_fin] using (products hot' a n (Fintype.card (Hot Γ)))
  apply exactConnected.trans
  calc
    _ ≤ c*h*b^D := mul_le_mul
      (mul_le_mul_of_nonneg_right mult hp) polynomial 
      (pow_nonneg (by positivity) _) (mul_nonneg cpos.le hp)
    _ ≤ _ := unit.2

end YM.Integration.WilsonReportEarlyConnected
end

