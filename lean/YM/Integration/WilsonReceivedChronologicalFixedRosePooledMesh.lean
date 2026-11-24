import YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalMesh
import YM.Integration.WilsonOriginalObservedRosePublicCurrency
import YM.Integration.WilsonOriginalTwoFlatIRPoolOrigins

/-! Buy every separately appointed pooled source's own j-to-K mesh on the original mixed grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRosePooledMesh
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

def width (A D:ℕ):ℕ:=A+D+1

theorem dated (simple:G.Simple)(A D:ℕ):
    ∀ᶠv:ℕ in atTop,∀{f K N per:ℕ},v≤f → f≤K → K≤N →
    σ K-σ (v-1)≤(A:ℝ)*(1+Real.log (heat v)) →
    σ K-σ v≤(2*A:ℕ)*Real.log (heat v) ∧
      σ K-σ (v-1)≤(width A D:ℝ)*(1+Real.log (heat v)) ∧
      ∀j:ℕ,a j/a f≤(heat f)^D → a j/a K≤((regulatorRun R.family N per v)⁻¹)^(aperture (width A D)):=by
  filter_upwards [WilsonReceivedChronologicalFixedRosePhysicalMesh.original R simple A 1 one_pos,
    WilsonOriginalObservedRosePublicCurrency.clock R simple (2*A) D,
    WilsonOriginalOpticalCouplingBand.cold R simple (max 1 ((4:ℝ)^D))]
    with v optical earned late f K N per vf fk kn span
  let z:=(regulatorRun R.family N per v)⁻¹
  have vk:=vf.trans fk
  obtain ⟨duration,ratio⟩:=optical (N:=N) (per:=per) vk kn span
  have opened:=late N per (vk.trans kn)
  have zp:1≤z:=(le_max_left ..).trans opened
  have power:(4:ℝ)^D≤z:=(le_max_right ..).trans opened
  have root:0≤Real.log (heat v):=Real.log_nonneg (R.family.path.levels.fits.delayed v).le
  have leWidth:(A:ℝ)≤(width A D:ℝ):=by exact_mod_cast (show A≤width A D by unfold width;omega)
  refine ⟨duration,span.trans (mul_le_mul_of_nonneg_right leWidth (by linarith only [root])),?_⟩
  intro j located
  have stock:(heat f)^D≤z*z^(2*D):=calc
    _ ≤ (heat K)^D:=pow_le_pow_left₀ (zero_le_one.trans (R.family.path.levels.fits.delayed f).le)
      (WilsonReflectedOpticalStock.monotone R simple fk) _
    _ ≤ (4:ℝ)^D*z^(2*D):=earned N per K vk kn duration
    _ ≤ _:=mul_le_mul_of_nonneg_right power (pow_nonneg (zero_le_one.trans zp) _)
  have top:a f/a K≤z^(aperture A):=(div_le_div_of_nonneg_right
    (R.family.S.strictAnti.antitone vf) (R.family.S.a_pos K).le).trans (ratio (a v) (by simp))
  calc a j/a K = (a j/a f)*(a f/a K):=by field_simp [(R.family.S.a_pos f).ne',(R.family.S.a_pos K).ne']
       _ ≤ (z*z^(2*D))*z^(aperture A):=mul_le_mul (located.trans stock) top
         (div_nonneg (R.family.S.a_pos f).le (R.family.S.a_pos K).le)
         (mul_nonneg (zero_le_one.trans zp) (pow_nonneg (zero_le_one.trans zp) _))
       _ = z^((2*D+1)+aperture A):=by rw [pow_add z (2*D+1),pow_succ z (2*D)];ring
       _ ≤ _:=pow_le_pow_right₀ zp (by unfold aperture width;omega)

variable {order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I](Jr:ℝ→tower S)(Z:WilsonPrescription G)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (A D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free R.family (d i).val)
    {δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃U:Set ℝ,U∈trail ∧ ∀ᶠv:ℕ in atTop,∀r∈U,
    ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∀{K N per:ℕ},v≤f → f≤K → K≤N →
    σ K-σ (v-1)≤(A:ℝ)*(1+Real.log (heat v)) →
      σ K-σ v≤(2*A:ℕ)*Real.log (heat v) ∧
      σ K-σ (v-1)≤(width A (2*T+11+2*h):ℝ)*(1+Real.log (heat v)) ∧
      ∀i,a (home F Jr Z (books (ρ i)) (d i) (x i)).j/a K≤
        ((regulatorRun R.family N per v)⁻¹)^(aperture (width A (2*T+11+2*h))):=by
  have sites:=WilsonMovingForkSlotDate.original F simple bliss slow D T h 0 d books
  refine ⟨_,sites,?_⟩
  filter_upwards [dated (R:=R) simple A (2*T+11+2*h)] with v date r ready ρ passed near f K N per vf fk kn span
  obtain ⟨duration,expanded,price⟩:=date (N:=N) (per:=per) vf fk kn span
  exact ⟨duration,expanded,fun i=>price _ ((ready ρ passed near
    (fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)) i).2.2.1)⟩

end YM.Integration.WilsonReceivedChronologicalFixedRosePooledMesh
