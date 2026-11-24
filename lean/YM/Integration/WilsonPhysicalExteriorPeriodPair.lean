import YM.Integration.WilsonPhysicalExteriorResolvedStage
import YM.Integration.WilsonPhysicalExteriorPrescribedSide
import YM.Integration.WilsonPhysicalExteriorMovingPeriod

/-! The original equilibrium period can be arbitrarily larger than the
independently prescribed small-field auxiliary torus: both are compared
on precisely the same subtracted field prescription and physical positions.
Their sizes are never equated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorPeriodPair
open Function Set Filter Real Lattice Precision RG PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Moving Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tide MS.Tone
open YM.FVAAlt2 FormalOPE
open WilsonPhysicalExteriorResolvedReadout WilsonPhysicalExteriorResolvedCutoff WilsonPhysicalExteriorUVStory
open scoped Topology BigOperators Classical

variable {G:Gauge} {K:KernelChoices} {X:Type}
variable (Y:Oracle.Program K)(Z:∀ b:Patch,b.Branches K G)(C:Run G)
variable (R:Lodge.Contract C Y Z)(t:X→ℕ)(ht:∀i,R.floor Y Z C≤t i)
local notation "track" => WilsonPhysicalExteriorRegulator.nativeTrack Y Z C R t ht
local notation "periods" => Period.Field.LodgeT.instance_real Y Z C R t ht
variable (F:Calibration.Tent (R.profile Y Z C t ht).entire)
variable {B:MS.Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)(τ:Prescription B) {n:ℕ}
variable {g:G.ColorIndex}{l:Filter X}{p:ℕ}
variable (hc:Calibration.Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native (R.profile Y Z C t ht).entire) F p)
    (hg:G.Simple) (hξ:Tendsto t l atTop) (hp:∀i,p≤t i)
    (hτ:TaylorOKPl M (Lobby.Table (basisR C) B) τ)

private theorem via (a z b:ℂ) : ‖a-b‖≤‖a-z‖+‖z-b‖ := by
  simpa only [dist_eq_norm] using dist_triangle a z b

def bank (μ:ℝ) (U:X→ Cover) (W:Fin n→X→ Cover) (Λ:X→ℝ) (D:Fin n→Label B) (k:ℕ) : X→ℂ :=
  Lobby.evaluateR C.metals.O (basisR C) τ D
    (WilsonPhysicalExteriorPrescribedSide.change ((track).PoseT μ U W) Λ) μ k

include hc hg hξ hp hτ in
theorem cover (μ:ℝ) (U:X→ Cover)(W:Fin n→X→ Cover)(D:Fin n→Label B) (k:ℕ)(hk:k≤p)
    (hU:(track).VenueT U) (hz:Reach ((track).PoseT μ U W).profile W)
    (hm:Resolved ((track).PoseT μ U W).profile (info W))
    (Λ:X→ℝ)(hΛ:Tendsto Λ l atTop) {d c:ℝ}(hc₂:c<2)(hθ:∀ᶠ i in l,(track).Θ i≤d*(Λ i)^c) :
    ∃ K₀:ℝ,0<K₀ ∧ ∀ᶠ i in l,
      ‖Lodge.physicalCover Y Z C R t ht F μ D U W τ k i-bank Y Z C R t ht τ μ U W Λ D k i‖≤
        K₀*exp (-mildG*(track).Θ i) := by
  let T:Trial X (Fin n):=(track).PoseT μ U W
  let Q:Trial X (Fin n):=WilsonPhysicalExteriorPrescribedSide.change T Λ
  have hQ : Domain Q l μ := WilsonPhysicalExteriorPrescribedSide.geometry T Λ hz hm (fun _=>rfl)
      ((track).θ_runs (R.batch_r Y Z C t ht hξ)) hΛ hc₂ hθ
  obtain ⟨_,K₁,h₁,ha⟩:=WilsonPhysicalExteriorResolvedStage.original Y Z C R t ht F μ p D
      hc hg hξ hp hτ U W hU hz hm k hk
  obtain ⟨_,K₂,h₂,hb⟩:=WilsonPhysicalExteriorResolvedReadout.measured C.metals.O (basisR C) τ D M
      C.alloy.B.ratio hQ hg hτ k
  refine ⟨K₁+K₂,add_pos h₁ h₂,?_⟩
  filter_upwards [ha,hb] with i a b
  let f:=Lodge.physicalCover Y Z C R t ht F μ D U W τ k i
  let z:=tour M D μ (testP T i) Finset.univ k
  let h:=bank Y Z C R t ht τ μ U W Λ D k i
  change ‖f-z‖≤K₁*exp (-mildG*(track).Θ i) at a
  change ‖h-z‖≤K₂*exp (-mildG*(track).Θ i) at b
  change ‖f-h‖≤_
  calc ‖f-h‖≤‖f-z‖+‖z-h‖:=via f z h
       _ ≤ K₁*exp (-mildG*(track).Θ i)+K₂*exp (-mildG*(track).Θ i) := by rw [norm_sub_rev z h];exact add_le_add a b
       _ = _ := by ring

variable (r E:X→ℝ) (hE:∀i,0<E i)(h:ℕ)
local notation "Menu" => Sound.Ethos.MenuF B h

include hc hg hξ hp hτ hE in
/-- Before the admitted field tuple, points, order, subtraction log, and
actual physical period, choose its lower threshold and interpolation charge.
The cutoff-independent physical subtraction is made at the literal auxiliary
side 4*(ceil(exp(Λ²))+1). The estimate keeps both independent remainders. -/
theorem finite :
  ∃ σ:X→ℕ,∃ A:ℝ,0≤A ∧ ∃ b:ℕ,∀ μ (U:X→ Cover)(W:Fin n→X→ Cover) (D:Fin n→Menu)
    k, k≤p → (track).VenueT U → Reach ((track).PoseT μ U W).profile W →
    Resolved ((track).PoseT μ U W).profile (info W) →
    (∀ i j,‖Tone.embed (U i+W j i)‖≤r i) → ∀ (Λ:X→ℝ),Tendsto Λ l atTop →
    ∀ {d c:ℝ},c<2 → (∀ᶠ i in l,(track).Θ i≤d*(Λ i)^c) →
    ∃ K₀:ℝ,0<K₀ ∧ ∀ᶠ i in l,∀ q, σ i≤q →
      ‖PowerSeries.coeff k (Sound.Figure.runPer C Z periods (fun i j=>U i+W j i) (Calibration.sheet F) q (track).stop
        (Sound.Ethos.owner∘D) τ (μ-(track).Θ i) (Sound.Alone track i) i) -
        bank Y Z C R t ht τ μ U W Λ (Sound.Ethos.owner∘D) k i‖ ≤
      A*(1+|μ|)^b*E i+K₀*exp (-mildG*(track).Θ i) := by
  obtain ⟨σ,A,hA,b,hb⟩:=WilsonPhysicalExteriorMovingPeriod.infrared (n:=n) Y Z C R t ht F τ r E hE h p
  refine ⟨σ,A,hA,b,?_⟩
  intro μ U W D k hk hU hz hm hr Λ hΛ d c hc₂ hθ
  obtain ⟨K₀,h₀,hK⟩:=cover Y Z C R t ht F M τ hc hg hξ hp hτ μ U W (Sound.Ethos.owner∘D) k hk hU hz hm Λ hΛ hc₂ hθ
  refine ⟨K₀,h₀,?_⟩
  filter_upwards [hK] with i hi
  intro q hq
  have hF:=hb i q hq D k hk (fun i j=>U i+W j i) (hr i) μ
  let χ := Lodge.physicalCover Y Z C R t ht F μ (Sound.Ethos.owner∘D) U W τ k i
  exact (via _ χ _).trans (add_le_add hF hi)

end YM.Integration.WilsonPhysicalExteriorPeriodPair
