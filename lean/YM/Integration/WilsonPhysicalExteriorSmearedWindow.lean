import YM.Integration.WilsonPhysicalExteriorCompactWindow

/-! A genuine separated smooth test of the regulated mixed rows. Both the
finite report and the independent MS report are evaluated on the actual
rounded positions. Compact support makes each separately Bochner integrable;
the quantitative bound uses the total variation of the original test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSmearedWindow
open Filter MeasureTheory Real Function Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone
open FVA2 Register FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorFirstCut WilsonPhysicalExteriorCompactWindow
open scoped Topology Classical
variable {G:Gauge} (R:Run G)
local notation "Λ₀" => RG16.Lambda R.family.path.levels
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
variable {n:ℕ} (c c':ℝ) (out:Fin n→Bool)
local notation "τ₀" => WilsonPhysicalExteriorActualSides.time R c
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R c'

private theorem chart : Continuous (Fountain.metric (m:=n)) := by
  apply continuous_pi
  intro i
  exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
    ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>E4)).continuous)

def cells (j:ℕ) (z:Points n) : Fin n→ Cover :=
  fun i=>positions R c c' out (Fountain.metric z) i j

private def phase (j:ℕ) (i:Fin n) (a:Axis) (z:Points n) : ℝ :=
  exp (τ₀ j) * (zoom (T₀ j) (out i) (Fountain.metric z i)) a

private theorem phased (j:ℕ) (i:Fin n) (a:Axis) :
    Continuous (phase R c c' out j i a) := by
  have h:Continuous (fun z:Points n=>(Fountain.metric z) i a) :=
    (continuous_apply a).comp ((continuous_apply i).comp chart)
  change Continuous (fun z:Points n=>exp (τ₀ j)*(zoom (T₀ j) (out i) (Fountain.metric z i)) a)
  cases e:out i
  · exact continuous_const.mul h
  · exact continuous_const.mul (continuous_const.mul h)

private theorem floor_eq (j:ℕ) (z:Points n) (i:Fin n) (a:Axis) :
    cells R c c' out j z i a=⌊phase R c c' out j i a z⌋ := by
  simp [cells,positions,Dial.assign,phase,Pi.smul_apply,smul_eq_mul]

private theorem measurable_cells (j:ℕ) : Measurable (cells R c c' out j) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro a
  simp only [floor_eq]
  exact Int.measurable_floor.comp (phased R c c' out j i a).measurable

private theorem sampled (f:Test n) (j:ℕ) (L:(Fin n→ Cover)→ℂ) :
    Integrable (fun z=>f z*L (cells R c c' out j z)) := by
  have lower (i:Fin n) (a:Axis) := f.hasCompactSupport.bddBelow_image
    (phased R c c' out j i a).continuousOn
  have upper (i:Fin n) (a:Axis) := f.hasCompactSupport.bddAbove_image
    (phased R c c' out j i a).continuousOn
  choose b hb using lower
  choose d hd using upper
  let B:Fin n→ Cover:=fun i a=>⌊b i a⌋
  let D:Fin n→ Cover:=fun i a=>⌊d i a⌋
  obtain ⟨A,hA⟩ := ((Set.finite_Icc B D).image (fun y=>‖L y‖)).bddAbove
  have hbound (z:Points n) (hz:z∈tsupport f) : ‖L (cells R c c' out j z)‖≤A := by
    apply hA
    refine ⟨cells R c c' out j z,⟨?_,?_⟩,rfl⟩
    · intro i a
      rw [floor_eq]
      exact Int.floor_mono (hb i a ⟨z,hz,rfl⟩)
    · intro i a
      rw [floor_eq]
      exact Int.floor_mono (hd i a ⟨z,hz,rfl⟩)
  have hf:Integrable (fun z=>f z) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hL:= (measurable_of_countable L).comp (measurable_cells R c c' out j)
  apply (hf.norm.mul_const A).mono' (f.continuous.measurable.mul hL).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz:z∈tsupport f
  · change ‖f z*L (cells R c c' out j z)‖≤‖f z‖*A
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound z hz) (norm_nonneg (f z))
  · have hw:f z=0:=by_contra fun h=>hz (subset_closure h)
    simp [hw]

def finite (Q:Prescription B₀) (D:Fin n→Label B₀) (side:Bool) (u:ℝ) (k j p:ℕ)
    (z:Points n) : ℂ :=
  Lobby.evaluateR R.metals.O (basisR R) Q D
    (scene R c (fun i _=>cells R c c' out j z i) side 0) u k (j,p)

def continuum (M:M₀) (D:Fin n→Label B₀) (u:ℝ) (k j p:ℕ) (z:Points n) : ℂ :=
  tour M D u (testP (WilsonPhysicalExteriorActualSides.field R c 0
    (fun i _=>cells R c c' out j z i)) (j,p)) Finset.univ k

private theorem held_row (M:M₀) (Q:Prescription B₀) (D:Fin n→Label B₀)
    (W:Fin n→ℕ→ Cover) (side:Bool) (u:ℝ) (k j p:ℕ) :
    signed R M Q D c (fun i _=>W i j) side k u (j,p)=signed R M Q D c W side k u (j,p) := by
  cases side <;> rfl

private theorem same_row (M:M₀) (Q:Prescription B₀) (D:Fin n→Label B₀) (side:Bool)
    (u:ℝ) (k j p:ℕ) (z:Points n) :
    finite R c c' out Q D side u k j p z-continuum R c c' out M D u k j p z=
      signed R M Q D c (positions R c c' out (Fountain.metric z)) side k u (j,p) := by
  exact held_row R c M Q D (positions R c c' out (Fountain.metric z)) side u k j p

private theorem legal (M:M₀) (Q:Prescription B₀) (D:Fin n→Label B₀) (side:Bool)
    (u:ℝ) (k j p:ℕ) (f:Test n) :
    Integrable (fun z=>f z*finite R c c' out Q D side u k j p z) ∧
    Integrable (fun z=>f z*continuum R c c' out M D u k j p z) := by
  exact ⟨sampled R c c' out f j (fun v=>
    Lobby.evaluateR R.metals.O (basisR R) Q D (scene R c (fun i _=>v i) side 0) u k (j,p)),
    sampled R c c' out f j (fun v=>tour M D u (testP
      (WilsonPhysicalExteriorActualSides.field R c 0 (fun i _=>v i)) (j,p)) Finset.univ k)⟩

private theorem wager (f:Test n) (F X:Points n→ℂ) (t e:ℝ) (pos:0<t)
    (iF:Integrable (fun z=>f z*F z)) (iX:Integrable (fun z=>f z*X z))
    (pt:∀z∈tsupport f,t*‖F z-X z‖≤e) :
    t*‖f.applyTo F-f.applyTo X‖≤e*∫z,‖f z‖ := by
  have hf:Integrable (fun z=>f z) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have price:‖∫z, f z*F z-f z*X z‖ ≤ ∫z, (e/t)*‖f z‖ := by
    apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz:z∈tsupport f
    · rw [←mul_sub,norm_mul,mul_comm (e/t)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (le_div_iff₀ pos).mpr (by simpa [mul_comm] using pt z hz)
    · have hw:f z=0:=by_contra fun h=>hz (subset_closure h)
      simp [hw]
  change t*‖(∫z,f z*F z)-(∫z,f z*X z)‖≤e*∫z,‖f z‖
  rw [←integral_sub iF iX]
  apply (mul_le_mul_of_nonneg_left price pos.le).trans_eq
  rw [integral_const_mul]
  field_simp

theorem tested {hG:G.Simple} (M:M₀) (Q:Prescription B₀)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q) (D:Fin n→Label B₀)
    (K:Set (Points n)) [Nonempty K]
    (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ) (A δ:ℝ) (ha:0<A) (hδ:0<δ)
    (bounded:∀z∈K,∀i,‖Fountain.metric z i‖≤A)
    (radial:∀z∈K,∀i,out i=true → δ≤‖Fountain.metric z i‖)
    (apart:∀z∈K,∀i l,i≠l → out i=out l → δ≤‖Fountain.metric z i-Fountain.metric z l‖)
    (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀ side:Bool,∀ p≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      ∀f:Test n,tsupport f⊆K → ∀u:ℝ,u=μ ∨ u=μ+R.family.S.scale j →
        let F:=finite R c c' out Q D side u k j p
        let X:=continuum R c c' out M D u k j p
        Integrable (fun z=>f z*F z) ∧ Integrable (fun z=>f z*X z) ∧
          (T₀ j)^h * ‖f.applyTo F - f.applyTo X‖ ≤ exp (-q*Λ₀ j) * ∫z, ‖f z‖ := by
  have raw:=measured R (hG:=hG) M Q rows D c c' out (fun z:K=>Fountain.metric z.1)
    slow h₁ h₂ h₃ lo A δ ha hδ (fun z=>bounded z.1 z.2) (fun z=>radial z.1 z.2)
    (fun z=>apart z.1 z.2) μ q k h
  filter_upwards [raw] with j hj side p hp f supp u hu
  obtain ⟨iF,iX⟩:=legal R c c' out M Q D side u k j p f
  refine ⟨iF,iX,wager f _ _ _ _ (pow_pos (exp_pos _) _) iF iX ?_⟩
  intro z hz
  rw [same_row]
  have a:=hj (⟨z,supp hz⟩:K) side p hp
  rcases hu with rfl|rfl
  · exact a.1
  · exact a.2

end YM.Integration.WilsonPhysicalExteriorSmearedWindow
