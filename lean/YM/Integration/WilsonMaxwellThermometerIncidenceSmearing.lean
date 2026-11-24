import YM.Integration.WilsonMaxwellThermometerIncidenceCells

/-! The genuine smeared seven-face public bare ground on its own finite
inversion. Each tuple receives its original compact test cell mass. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerIncidenceSmearing
open Filter Set Finset Function Metric MeasureTheory Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement
open WilsonMaxwellThermometerBareIncidenceRate (assembled)
open WilsonMaxwellThermometerConnectedIncidenceRate (row)
open WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells (weight)
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)

def read (M:Mesh) (o:M.Tuple (n:=3)) (p:Tags G 6 3):ℂ:=
  row (live W 6 (translated M (Mesh.back M o)) 0) p

theorem at_cell (M:Mesh)(x:Points 3)(p:Tags G 6 3):
    read W M (cell M x) p=row (live W 6 (translated M (Extraction.address M.spacing x)) 0) p:=by
  let v:=Mesh.back M (cell M x)
  let w:=Extraction.address M.spacing x
  have wrapped:wrap M.p.side ∘ v=wrap M.p.side ∘ w:=by
    funext i;exact wrap_lift _
  have same:chartV (translated M v)=chartV (translated M w):=by
    funext i
    have eq:=congrFun wrapped i
    change wrap M.p.side (v i+shift M)=wrap M.p.side (w i+shift M)
    simpa only [map_add,Function.comp_apply] using congrArg (· + wrap M.p.side (shift M)) eq
  have raw:live W 6 (translated M v) 0=live W 6 (translated M w) 0:=by
    unfold Cirrus.live
    simp only [same]; rfl
  exact congrArg (fun q=>row q p) raw

def integrated (φ:Test 3)(M:Mesh)(p:Tags G 6 3):ℂ:=
  ∑o:M.Tuple (n:=3),weight φ (cell M) o * read W M o p

private theorem original_integrable (φ:Test 3)(M:Mesh)(p:Tags G 6 3):
    Integrable (fun x=>φ x*read W M (cell M x) p):=by
  have funded:Integrable (fun x:Points 3=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  let B:=∑o:M.Tuple (n:=3),‖read W M o p‖
  have h (x:Points 3):‖read W M (cell M x) p‖≤B:=
    single_le_sum (f:=fun o=>‖read W M o p‖) (fun o _=>norm_nonneg _) (mem_univ _)
  exact (funded.norm.mul_const B).mono' (φ.continuous.measurable.mul
    ((measurable_of_countable (fun o=>read W M o p)).comp (measurable_cell M))).aestronglyMeasurable
    (ae_of_all _ fun x=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _))

theorem original (φ:Test 3){I:Fin 3→Type}[∀j,Fintype (I j)](f:∀j,I j→Sec G 6):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀v:∀j,I j→ℂ,
      ‖integrated W φ M (assembled 6 f v)-φ.applyTo (fun x=>
        WilsonMaxwellThermometerFaces.connected x (assembled 6 f v))‖≤
        ((∫x:Points 3,‖φ x‖)*C*M.spacing)*∏j,∑i,‖v j i‖:=by
  obtain ⟨C,pos,sale⟩:=WilsonMaxwellThermometerIncidenceCells.original W f
    φ.hasCompactSupport φ.tsupport_subset
  refine ⟨C,pos,?_⟩
  filter_upwards [sale] with M fee
  intro v
  let p:=assembled 6 f v
  let g (x:Points 3):ℂ:=WilsonMaxwellThermometerFaces.connected x p
  have smooth:ContinuousOn g (conf 3):=by
    intro x hx
    have hk (s:Badge):ContinuousAt (fun z:Points 3=>WilsonMaxwellThermometerFaces.faces z p s) x:=
      (Wick.moment_smooth (fun j=>(missing p s j).val) hx).continuousAt
    change ContinuousWithinAt (fun z=>PowerSeries.constantCoeff (b3 (fun s=>
      PowerSeries.C (WilsonMaxwellThermometerFaces.faces z p s)))) _ _
    simp [b3,Algebra.smul_def]
    fun_prop (disch:=intros; apply (hk _).continuousWithinAt)
  have htarget:Integrable (fun x=>φ x*g x):=φ.smearing smooth
  have hsource:=original_integrable W φ M p
  have htest:Integrable (fun x:Points 3=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  let δ:ℝ:=(C*M.spacing)*∏j,∑i,‖v j i‖
  have hearing:∀ x,‖φ x*read W M (cell M x) p-φ x*g x‖≤‖φ x‖*δ:=by
    intro x
    rw [←mul_sub,norm_mul]
    by_cases h:x∈tsupport φ
    · exact mul_le_mul_of_nonneg_left (by simpa only [at_cell] using fee x h v) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport h];simp only [norm_zero,zero_mul,le_refl]
  have exact_credit:integrated W φ M p=φ.applyTo (fun x=>read W M (cell M x) p):=
    (WilsonSeparatedOriginalThermometerCells.tested φ (cell M) (measurable_cell M) (fun o=>read W M o p)).symm
  change ‖integrated W φ M p-φ.applyTo g‖≤_
  rw [exact_credit,Test.applyTo,Test.applyTo,←integral_sub hsource htarget]
  calc
    _≤∫x:Points 3,‖φ x*read W M (cell M x) p-φ x*g x‖:=norm_integral_le_integral_norm _
    _≤∫x:Points 3,‖φ x‖*δ:=integral_mono (hsource.sub htarget).norm (htest.norm.mul_const δ) hearing
    _= _:=by rw [integral_mul_const];simp only [δ];ring

end YM.Integration.WilsonMaxwellThermometerIncidenceSmearing
