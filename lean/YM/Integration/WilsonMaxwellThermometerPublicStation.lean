import YM.Integration.WilsonMaxwellThermometerPublicGalop

/-! The first position coefficient can be read on the actual nominated finer
aligned date. The three original cutoff cell masses are unchanged and each
registered upper site is coarsened along that very trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicStation
open Function Set Filter Finset Metric MeasureTheory Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)
variable (s:ℝ→ℕ)

def aperture (r:ℝ):ℝ:=if 0<r then R.family.S.a (s r)/r else 1

theorem granted (r:ℝ):0<aperture R s r:=by
  unfold aperture
  split_ifs with pos
  · exact div_pos (R.family.S.a_pos _) pos
  · exact zero_lt_one

theorem shrinking_at (simple:G.Simple)(B:ℕ)(pos:0<B)
    (finer:∀ᶠ r in trail,WilsonMeasuredWindow.stop R.family.path.levels simple B r ≤ s r):
    Tendsto (aperture R s) trail (𝓝 0):=by
  apply squeeze_zero' (Eventually.of_forall fun r=>(granted R s r).le) _ (shrinking R simple B pos)
  filter_upwards [finer,self_mem_nhdsWithin (s:=Set.Ioi 0)] with r h hr
  rw [aperture,spacing,if_pos (show 0<r from hr),if_pos (show 0<r from hr)]
  exact div_le_div_of_nonneg_right (R.family.S.strictAnti.antitone h) hr.le

local notation "μ" => (fun (r : ℝ) (per : ℕ) =>
  chart R (s r) per (aperture R s r) (granted R s r))

def filed (r : ℝ) (z : ℕ×ℕ) : Point G 6 3 :=
  if h : s r ≤ z.1 then
    ∑ o, weight (Rose.test K) (positions (R:=R) r z) o •
      atSites W (V:=V) (μ r z.2) ((R.family.S.toDepth h z.2).parent ∘ o)
  else 0

theorem fixed (f : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤f.fuse)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (p : Tags G 6 3) :
    Tendsto (fun w : ℝ×(ℕ×ℕ)=>filed R W K s w.1 w.2 p) (trail.curry U)
      (𝓝 ((Rose.test K).applyTo (fun x=>continuum W (V:=V) x p))) := by
  let M := ∫ x : Points 3,‖Rose.test K x‖
  have nonneg : 0≤M := integral_nonneg fun _=>norm_nonneg _
  have geo := reporting R trail f U prior s _ (granted R s) small
  have gates : ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U,0<w.1 ∧ s w.1≤w.2.1 := by
    apply eventually_curry_iff.mpr
    filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi 0)] with r pos
    exact ((large_mesh f (s r)).filter_mono prior).mono fun _g hi=>⟨pos,hi⟩
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let δ := ε/(M+1)
  have pos : 0<δ := div_pos he (by positivity)
  filter_upwards [gates,geo.eventually (nearby W K p pos)] with w gate due
  rcases w with ⟨r,z⟩
  let g := R.family.S.toDepth gate.2 z.2
  let a := μ r z.2
  let χ := positions (R:=R) r z
  let sample := fun o=>atSites W (V:=V) a (g.parent ∘ o) p
  have cash (x) (hx : x∈tsupport (Rose.test K)) :
      dist (sample (χ x)) (continuum W (V:=V) x p) ≤ δ := by
    obtain ⟨v,hs,good⟩ := WilsonMaxwellThermometerParentLift.parents R.family.S gate.2 z.2 gate.1 x
    have agree : atSites W (V:=V) a (g.parent ∘ χ x) = sampled W (V:=V) (translated a v) := by
      apply same_sites
      refine Eq.trans ?_ hs.symm
      funext i
      exact wrap_lift _
    dsimp only [sample]
    rw [agree]
    apply due x hx
    simpa only [a,chart,aperture,if_pos gate.1] using good
  have bill := WilsonMaxwellThermometerFirstCells.test_price W K χ (placed (R:=R) r z) sample p δ cash
  rw [tested (Rose.test K) χ (placed (R:=R) r z) sample] at bill
  rw [dist_eq_norm,filed,dif_pos gate.2,_root_.sum_apply]
  simp only [_root_.smul_apply,smul_eq_mul]
  refine bill.trans_lt ?_
  change M*(ε/(M+1))<ε
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity)]
  nlinarith

def report (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):ℂ:=
  if h:s r≤z.1 then
    ∑o,weight (Rose.test K) (positions (R:=R) r z) o •
      WilsonMaxwellThermometerPublicGalop.node W (V:=V)
        (translated (μ r z.2) (Mesh.back (μ r z.2) ((R.family.S.toDepth h z.2).parent ∘ o))) p
  else 0

theorem quotient (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):
    filed R W K s r z p=report R W K s r z p:=by
  by_cases h:s r≤z.1
  · simp only [filed,report,dif_pos h,_root_.sum_apply,smul_apply,atSites,
      WilsonMaxwellThermometerPublicGalop.enrolled]
  · simp only [filed,report,dif_neg h,zero_apply]

variable {R} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ→tower S) {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
    (A : ℝ→Group R.family 6)
local notation "A'" => WilsonPositionCorrectedCap.adjusted F J V A
local notation "v" => WilsonPositionGradedThermometerGround.tags

theorem original (simple:G.Simple)(B:ℕ)(hB:0<B)
    (finer:∀ᶠ r in trail,WilsonMeasuredWindow.stop R.family.path.levels simple B r ≤ s r)
    (prior : (Y:Filter _)≤f.fuse) (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J) :
    Tendsto (fun w : ℝ×(ℕ×ℕ)=>report R W K s w.1 w.2 (v (A' w.1)))
      (trail.curry (Y:Filter _)) (𝓝 ((Rose.c_T K:ℝ):ℂ)) := by
  simp_rw [←quotient]
  have radius : Tendsto (Prod.fst : ℝ×(ℕ×ℕ)→ℝ) (trail.curry (Y : Filter _)) trail :=
    tendsto_fst.mono_left Filter.curry_le_prod
  rw [← WilsonMaxwellThermometerFirstDetector.normalized W K simple]
  exact lights 6 _ _ (fun i=>(WilsonMaxwellThermometerFirstPosition.fitted F J A book lead i).comp radius)
    _ (smeared W K) (fixed R W K s f _ prior (shrinking_at R s simple B hB finer))

end YM.Integration.WilsonMaxwellThermometerPublicStation
