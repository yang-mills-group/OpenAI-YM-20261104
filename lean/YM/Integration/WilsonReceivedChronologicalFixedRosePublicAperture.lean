import YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalMesh
import YM.Integration.WilsonOriginalObservedRosePublicCurrency
import YM.Integration.WilsonOriginalTwoFlatIRPoolOrigins

/-! Buy every separately appointed pooled source's own j-to-K mesh on the original mixed grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRosePublicAperture
open Function Filter Finset Set Lattice RG Wilson Source Extraction Table Spec Trace.Pilot
open PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Pert.Asymptotics
open PhysMS FVA2 FVA2.Register MS.Land
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalObservedRosePublicMesh (aperture)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}
local notation "heat" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale


open WilsonInvariantActionPosition (berth)

def width (reserve trust:ℕ):ℕ:=trust+reserve+1

theorem dated (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(reserve trust:ℕ):
    ∀clock:ℕ,∀ᶠv:ℕ in atTop,∀{f N per:ℕ},v≤f →
    let K:=berth R reserve f
    f≤K → K≤N → σ K-σ (v-1)≤(clock:ℝ)*(1+Real.log (heat v)) →
    σ K-σ v≤(2*clock:ℕ)*Real.log (heat v) ∧
      ∀j:ℕ,a j/a f≤(heat f)^trust → a j/a K≤((regulatorRun R.family N per v)⁻¹)^(aperture (width reserve trust)):=by
  intro clock
  let m:=width reserve trust
  obtain ⟨onset,openAt⟩:=eventually_atTop.mp (WilsonAddressedCollarWindow.original R simple slow reserve (η:=1) zero_lt_one)
  filter_upwards [eventually_ge_atTop onset,WilsonReceivedChronologicalFixedRosePhysicalMesh.original R simple clock 1 one_pos,
    WilsonOriginalObservedRosePublicCurrency.clock R simple (2*clock) m,
    WilsonOriginalOpticalCouplingBand.cold R simple (max 1 ((4:ℝ)^m))]
      with v mature time thermal ready f N per vf K fk kn span
  let z:=(regulatorRun R.family N per v)⁻¹
  have duration:σ K-σ v≤(2*clock:ℕ)*Real.log (heat v):=(time (per:=per) (vf.trans fk) kn span).1
  have raw:a f/a K≤(heat f)^(reserve+1):=by
    simpa only [pow_succ,Real.rpow_one] using (openAt f (mature.trans vf)).2.2
  have heatp:0≤heat f:=zero_le_one.trans (R.family.path.levels.fits.delayed f).le
  have opened:=ready N per ((vf.trans fk).trans kn)
  have zp:1≤z:=(le_max_left ..).trans opened
  have constant:(4:ℝ)^m≤z:=(le_max_right ..).trans opened
  have earned:(heat f)^m≤z*z^(2*m):=calc
    _≤(heat K)^m:=pow_le_pow_left₀ heatp (WilsonReflectedOpticalStock.monotone R simple fk) _
    _≤(4:ℝ)^m*z^(2*m):=thermal N per K (vf.trans fk) kn duration
    _≤_:=mul_le_mul_of_nonneg_right constant (pow_nonneg (zero_le_one.trans zp) _)
  refine ⟨duration,?_⟩
  intro j placed
  calc a j/a K=(a j/a f)*(a f/a K):=by field_simp [(R.family.S.a_pos f).ne',(R.family.S.a_pos K).ne']
       _≤(heat f)^trust*(heat f)^(reserve+1):=mul_le_mul placed raw
         (div_nonneg (R.family.S.a_pos f).le (R.family.S.a_pos K).le) (pow_nonneg heatp _)
       _=(heat f)^m:=by rw [←pow_add];congr 1
       _≤z*z^(2*m):=earned
       _=z^(2*m+1):=by rw [pow_succ];ring
       _≤_:=pow_le_pow_right₀ zp (by dsimp only [m,aperture];omega)

variable {order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I](Jr:ℝ→tower S)(Z:WilsonPrescription G)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (reserve D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free R.family (d i).val)
    {δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃U:Set ℝ,U∈trail ∧ ∀clock:ℕ,∀ᶠv:ℕ in atTop,∀r∈U,
    ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    let K:=berth R reserve f
    ∀{N per:ℕ},v≤f → f≤K → K≤N →
    σ K-σ (v-1)≤(clock:ℝ)*(1+Real.log (heat v)) →
      σ K-σ v≤(2*clock:ℕ)*Real.log (heat v) ∧
      ∀i,a (home F Jr Z (books (ρ i)) (d i) (x i)).j/a K≤
        ((regulatorRun R.family N per v)⁻¹)^(aperture (width reserve (2*T+11+2*h))):=by
  have sites:=WilsonMovingForkSlotDate.original F simple bliss slow D T h 0 d books
  refine ⟨_,sites,?_⟩
  intro clock
  filter_upwards [dated (R:=R) simple slow reserve (2*T+11+2*h) clock] with v date r ready ρ passed near f K N per vf fk kn span
  obtain ⟨duration,price⟩:=date (N:=N) (per:=per) vf fk kn span
  exact ⟨duration,fun i=>price _ ((ready ρ passed near
    (fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)) i).2.2.1)⟩

end YM.Integration.WilsonReceivedChronologicalFixedRosePublicAperture
