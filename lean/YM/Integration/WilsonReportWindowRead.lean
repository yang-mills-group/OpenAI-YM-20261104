import YM.Integration.WilsonReportWindowRoster
import YM.Integration.WilsonReportColumnSuppression
import YM.Integration.WilsonReportRegularMoments
import YM.Integration.WilsonReportConnectedCurrency

/-! Joint raw and connected finite-window measurements of every marking on
the true common report. The original ultraviolet moment and the preceding
reports are compared before the fine cutoff and the torus, with the complete
Möbius subtraction and the actual mutually disjoint source apertures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowRead
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Cells OPE.Strobe.Panoramic Push.GridApprox WilsonReportColumnCut
open Extra.Trajectories (connected)
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportMomentDifference
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

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

private theorem settle {a b c K h v cap g : ℝ} (P D : ℕ)
    (ha : 1≤a) (mono : a≤b) (hK : 0≤K) (hv : 0≤v) (hc : 1≤c) (hp : 0≤h)
    (hc₀ : cap≤1) (g0 : 0≤g) (g1 : g≤1)
    (early : (2*c)*h*a^D≤cap*g)
    (cut : (2*c*(1+K))*(v*b^(P+D))≤cap*g) :
    let e := K*(v*b^P)
    h+e≤1 ∧ c*(h+e)*a^D≤cap*g := by
  let e := K*(v*b^P)
  have a0 := zero_le_one.trans ha
  have b0 := a0.trans mono
  have c0 := zero_le_one.trans hc
  have e0 : 0≤e := mul_nonneg hK (mul_nonneg hv (pow_nonneg b0 _))
  have sup : (2*c)*e*a^D ≤ (2*c*(1+K))*(v*b^(P+D)) := by
    have left : (2*c)*K≤2*c*(1+K) := by nlinarith only [c0]
    calc
      _ = ((2*c)*K)*(v*b^P)*a^D := by dsimp only [e]; ring
      _ ≤ (2*c*(1+K))*(v*b^P)*b^D :=
        mul_le_mul (mul_le_mul_of_nonneg_right left (mul_nonneg hv (pow_nonneg b0 _)))
          (pow_le_pow_left₀ a0 mono _) (pow_nonneg a0 _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have total : c*(h+e)*a^D≤cap*g := by nlinarith only [early,sup.trans cut]
  dsimp only
  refine ⟨?_,total⟩
  have e1 := le_mul_of_one_le_left (add_nonneg hp e0) hc
  exact (e1.trans (le_mul_of_one_le_right (mul_nonneg c0 (add_nonneg hp e0)) (one_le_pow₀ ha))).trans
    (total.trans (mul_le_one₀ hc₀ g0 g1))

private theorem amplitude {a b : ℝ} (p : ℕ) (ha : 5≤a) (b0 : 0≤b) (close : b≤2*a) :
    5*b^p≤a^(1+2*p) := by
  have a0 : 0≤a := by linarith only [ha]
  have width : b≤a^2 := close.trans (by nlinarith only [mul_le_mul_of_nonneg_right ha a0,a0])
  calc
    _ ≤ a*(a^2)^p := mul_le_mul ha (pow_le_pow_left₀ b0 width _) (pow_nonneg b0 _) a0
    _ = _ := by rw [←pow_mul,pow_add,pow_one]

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
      let localField (j : Fin n) := localized L r (d j) k N p (w j) (x j)
      (∀ j,Interior (window (x j) (omen C (d j) k B)) (localField j)) ∧
      (∀ i j : Fin n,i≠j→Disjoint (window (x i) (omen C (d i) k B)) (window (x j) (omen C (d j) k B))) ∧
      (∀ A : Finset (Fin n), ‖moment (C.beta N p) (fun U=>∏j∈A,fine L d w r cut.le x j U)-
        ∫U,∏j∈A,localField j U ∂(Therm.scene C.path N p k)‖≤ε*(g r)^q) ∧
      ∀ s : Γ.Mode,
      ‖(connected (microscopic Γ C (fine L d w r cut.le x))).part s -
        (connected (reported Γ C (N:=N) localField)).part s‖ ≤ ε*(g r)^q := by
  intro o q power ε hε
  let Ω : Census (Fin n) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  choose e invoices using fun j : Fin n => (paying (d j)).affordability
  let labels := (∑ j,e j)+power
  refine ⟨labels,?_⟩
  let order := 1+(o+27)*((∑ j,d j)+1)
  let a := 1+2*(order+labels)
  let D := (a*n+1)*Fintype.card (Hot Γ)
  let E := q+D+1
  let c := 1+∑ s : Γ.Mode,WilsonReportMomentDifference.multiplicity Γ s
  have cpos : 0<c := by
    dsimp only [c]
    linarith only [sum_nonneg (s:=univ) (fun (s : Γ.Mode) _=>multiple Γ s)]
  have c1 : 1≤c := le_add_of_nonneg_right (sum_nonneg (fun (s : Γ.Mode) _=>multiple Γ s))
  let K₀ := (2:ℝ)*n*5^n
  have k0 : 0≤K₀ := by dsimp only [K₀]; positivity
  let P := (order+labels)*(n+1)
  let cap := min ε 1
  have cap₀ : 0<cap := lt_min hε zero_lt_one
  have c2 := mul_pos (by norm_num : (0:ℝ)<2) cpos
  have fees := WilsonReportConnectedCurrency.absorb R hG pace hB g hg D q c2 cap₀
  have trim := WilsonReportColumnSuppression.price hG pace hB g hg (P+D) q
    (mul_pos c2 (by linarith only [k0] : 0<1+K₀)) cap₀ pegs.level.growing placed
  have widths := eventually_all.mpr (fun j : Fin n=>WilsonReportColumnSuppression.width (R:=R) hG (d j))
  obtain ⟨whereAt,wide⟩ := eventually_atTop.1 widths
  have attained := pegs.level.growing.eventually_ge_atTop whereAt
  have small := (Trace.Pilot.Coupling.conforms hG hg).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))
  dsimp only at fees
  rw [←placed] at fees
  have flags := scene.allFlags Ω d o t E labels ht
  have grades := eventually_all.mpr fun j : Fin n=>pegs.level.growing.eventually_ge_atTop (R.family.ref (d j))
  have zero := pegs.level.growing.eventually_ge_atTop (R.family.ref 0)
  have warmth := ((Next.Rank.Station.hat_rate R.family.path.levels hG).comp pegs.level.growing).eventually_ge_atTop (5:ℝ)
  have positive_r : ∀ᶠ r : ℝ in RG17.home,0<r := self_mem_nhdsWithin
  filter_upwards [flags,eventually_all.mpr invoices,fees,grades,zero,warmth,attained,trim,hg.positive,small,positive_r] with
    r flag reps tariff grade g0 hot late trim gp modest hr
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
  have budget (j) : mass R.family (d j) (L.shift (d j) r (w j))≤b^labels := by
    calc
      _ ≤ b^e j*‖v j‖ := cost j
      _ ≤ b^e j*b^power := mul_le_mul_of_nonneg_left (hv j) (pow_nonneg b0 _)
      _ = b^(e j+power) := (pow_add ..).symm
      _ ≤ b^labels := pow_le_pow_right₀ b1 (Nat.add_le_add_right
        (Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (mem_univ j)) power)
  refine ⟨w,agrees,budget,?_⟩
  intro X hX p
  obtain ⟨sample,earlier⟩ := table X (stays X hX) p
  refine ⟨sample,?_⟩
  intro N cut x neighbor
  let β := R.family.path.levels.clock.hatBeta k
  let B₀ := (R.family.path.levels.budget k).B
  let WW (j : Fin n) := localized L r (d j) k N p (w j) (x j)
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
  obtain ⟨holds,bound,clipped⟩ := WilsonReportWindowRoster.retained hG W original subsidy L services r d w
    grade (g0.trans_lt deep) deep.le cut cover.zoom budget x
  refine ⟨holds,?_,?_⟩
  · intro i j ij
    let D₀ (v : Fin n) := omen R.family (d v) k B₀
    have large := wide k (late.trans deep.le)
    have di : 2*D₀ i < B₀^8 := large i
    have dj : 2*D₀ j < B₀^8 := large j
    have sum : D₀ i+D₀ j < B₀^8 := by omega
    have apart := sum.trans_le (cover.extra.trans ((fitsSnap R ht (stays X hX) hr cover x neighbor).2.1 i j ij))
    apply Set.disjoint_left.mpr
    intro y left right
    have triangle := separation_triangle (x i) y (x j)
    rw [separation_comm y (x j)] at triangle
    exact (not_le_of_gt apart) (triangle.trans (Nat.add_le_add (sparrow.mp left) (sparrow.mp right)))
  have bb0 : 0≤β := zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have bounded (j : Fin n) (U) : ‖WW j U‖ ≤ b^a :=
    (bound j U).trans (amplitude (order+labels) hot bb0 cover.compat)
  let amp := Real.exp (-2*(B₀:ℝ))
  let saved := K₀*(amp*β^P)
  have e0 : 0 ≤ saved := mul_nonneg k0 (mul_nonneg (Real.exp_nonneg _) (pow_nonneg bb0 _))
  have mono : b≤β := WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos hG).le deep.le
  obtain ⟨raw,fee⟩ := settle P D b1 mono k0 (Real.exp_nonneg (-2*(B₀:ℝ))) c1 hp
    (min_le_right ε 1) (pow_nonneg gp.le q) (pow_le_one₀ gp.le modest.le)
    (show (2*c)*h*b^D≤cap*(g r)^q from unit.2) (trim k deep.le)
  have slots (A : Finset (Fin n)) : ‖moment (R.family.beta N p) (fun U=>∏j∈A, FF j U)-
      (∫U,∏j∈A, WW j U ∂OPE.Therm.scene R.family.path N p k)‖≤h+saved :=
    (norm_sub_le_norm_sub_add_norm_sub _ (∫U,∏j∈A,SS j U ∂OPE.Therm.scene R.family.path N p k) _).trans
      (add_le_add (physical A) (clipped A).2)
  refine ⟨?_,?_⟩
  · intro A₀
    have small₀ := le_mul_of_one_le_left (add_nonneg hp e0) c1
    exact (slots A₀).trans ((small₀.trans (le_mul_of_one_le_right (mul_nonneg cpos.le (add_nonneg hp e0))
      (one_le_pow₀ b1))).trans (fee.trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp.le _))))
  intro s
  have exactConnected := WilsonReportMomentDifference.original Γ R.family R.makes cut.le FF WW (add_nonneg hp e0)
    raw (one_le_pow₀ b1) bounded slots s
  have mult : WilsonReportMomentDifference.multiplicity Γ s≤c := by
    dsimp only [c]
    have all := single_le_sum (f:=WilsonReportMomentDifference.multiplicity Γ) (fun j _=>multiple Γ j) (mem_univ s)
    linarith only [all]
  have hot' : 2≤b := (show (2:ℝ)≤5 by norm_num).trans hot
  have polynomial : (1+(b^a)^Fintype.card (Fin n))^Fintype.card (Hot Γ)≤b^D := by
    simpa only [D,Fintype.card_fin] using (products hot' a n (Fintype.card (Hot Γ)))
  apply exactConnected.trans
  calc
    _ ≤ c*(h+saved)*b^D := mul_le_mul
      (mul_le_mul_of_nonneg_right mult (add_nonneg hp e0)) polynomial
      (pow_nonneg (by positivity) _) (mul_nonneg cpos.le (add_nonneg hp e0))
    _ ≤ _ := fee.trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp.le _))

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
      let localField (j : Fin n) := localized L r (d j) k N p (w j) (x j)
      (∀ j,Interior (window (x j) (omen C (d j) k B)) (localField j)) ∧
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

end YM.Integration.WilsonReportWindowRead
end

