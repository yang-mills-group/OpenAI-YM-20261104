import YM.Integration.WilsonPhysicalRegisteredLocalAction
import YM.Integration.WilsonPositionSeparatedProfileFittedPrimary
import YM.Next.MULTISOURCE.Stencil

/-! The actual registered source stencils, with one fixed radius chosen before
the period or placement. The same larger cold windows pay the error in the
lower, normalized physical readings and admit the genuine local gauge chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingRegisteredAction
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open OPE.Therm RG05Readout Address Native Pulse MergeProof Accent Axial Work.E08
open PhysicalNext.Repeat.Legato WilsonReportingPlaquetteWindows WilsonReportingRegisteredWindows
open WilsonPositionSeparatedProfileReportingPrimary WilsonPositionSeparatedProfileReportingWindow
open WilsonPositionSeparatedProfileReportingCut
open WilsonPhysicalRegisteredLocalAction MSbar.Heath PertExtension
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [DecidableEq I]

/-- Torus-independent integer determined by the original finite stencil. -/
def depth (d : ℕ) := (R.family.localSection d).stencil.sup fun x => Finset.univ.sup fun i => (x i).natAbs

theorem reaches {n : Side} (d : ℕ) (o x : Site n) (hx : x∈(R.family.localSection d).footprint o) :
    separation o x ≤ depth R d := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  rw [separation_comm,separation,add_sub_cancel_right]
  exact Finset.sup_le fun i _ => (Corona.lap _ _).trans ((Finset.le_sup (f:=fun i => (y i).natAbs)
    (Finset.mem_univ i)).trans (Finset.le_sup (s:=(R.family.localSection d).stencil)
      (f:=fun x => Finset.univ.sup fun i => (x i).natAbs) hy))

def faces {n : Side} (d : ℕ) (o : Site n) := WilsonAxialWindow.cells o (depth R d+3)

def bonds {n : Side} (d : ℕ) (o : Site n) : Finset (Edge (Site n)) :=
  let X:=(R.family.localSection d).footprint o
  Finset.univ.filter fun e => e.1∈X ∧ e.1+step e.2∈X

theorem covers {n : Side} (d : ℕ) (o : Site n) :
    cover ((R.family.localSection d).footprint o) ⊆ faces R d o := by
  intro z hz
  obtain ⟨a,ha,dx⟩ := halo_spec.mp (Finset.mem_product.mp hz).1
  have dist := (separation_triangle o a z.1).trans (Nat.add_le_add (reaches R d o a ha) dx)
  have liftbox := Work.E08.lift_mem_box (dist.trans (show depth R d+2≤depth R d+3 by omega))
  have cell := WilsonAxialWindow.cell o (depth R d+3) liftbox z.2
  simpa [faces,wrap_lift] using cell

private theorem large {C η : ℝ} (he : 0<η) (A : Levels G) (simple : G.Simple) :
    ∀ᶠ k:ℕ in atTop, C*cool A k≤η := by
  have rate := Next.Rank.Station.hat_rate A simple
  filter_upwards [rate.eventually (Extra.Multi.hat_affords (C*2^12/η) 12)] with k hk
  let x:=A.clock.hatBeta k
  have h:(C*2^12/η)*(Real.log x/2)^12*(Real.sqrt x)⁻¹≤1:=hk
  rw [div_pow] at h
  apply (div_le_one₀ he).mp
  change (C*((Real.sqrt x)⁻¹*(Real.log x)^12))/η≤1
  calc
    _=(C*2^12/η)*(Real.log x^12/2^12)*(Real.sqrt x)⁻¹:=by field_simp
    _≤1:=h

omit [DecidableEq I] in
/-- Every placement of each submitted source has the same finite preselected
upper bound on its face count, and on that true cold event its inner links are
simultaneously in the exponential chart after a gauge supported on the stencil. -/
theorem admitted (simple : G.Simple) (d : I→ℕ) (J : Voice G) (clear : Clear G J) {r : ℝ} (pr : 0<r) :
    ∃ b:ℝ,0<b ∧ ∀ᶠ k:ℕ in atTop,∀per i (o : Site (R.family.side k per)),
      ((faces R (d i) o).card:ℝ)≤R.family.path.levels.clock.hatBeta k ∧
      ∀U∈House.chilly (faces R (d i) o) (cool R.family.path.levels k),
      let B:=(R.family.localSection (d i)).footprint o
      let E:=bonds R (d i) o
      0<(colors G _).real (window B E U b) ∧ ∀z∈window B E U b,
        (fun e : ↥E => Lattice.gauge (change B z) U e.val)∈Chart.chamber G (↥E) r := by
  let A:=R.family.path.levels
  let δ:=min J.δ (r/J.C)
  have pc:=zero_lt_one.trans_le clear.cost
  have positive:0<δ:=lt_min clear.dist (div_pos pr pc)
  have size: J.C*δ≤r := by rw [mul_comm];exact (le_div_iff₀ pc).mp (min_le_right ..)
  let D (i:I):=depth R (d i)+3
  let cost (i:I):ℕ:=(D i+D i+1)^4*Fintype.card PlaqAxes
  have meter:=Next.Rank.Station.hat_rate A simple
  have price:∀ᶠ k:ℕ in atTop,∀i,(cost i:ℝ)≤A.clock.hatBeta k:=
    eventually_all.mpr fun i=>meter.eventually_ge_atTop (cost i)
  have room:∀ᶠ k:ℕ in atTop,∀i,4*(D i:ℝ)*Fintype.card PlaqAxes*cool A k≤δ/2 :=
    eventually_all.mpr fun i=> large (half_pos positive) A simple
  have period:∀ᶠ k:ℕ in atTop,∀i,2*D i<(A.S.denominator k).val:=
    eventually_all.mpr fun i=>A.S.den_strict.tendsto_atTop.eventually_gt_atTop (2*D i)
  refine ⟨δ,positive,?_⟩
  filter_upwards [price,room,period] with k paid width wide per i o
  constructor
  · exact (by exact_mod_cast WilsonAxialWindow.count o (D i) : ((faces R (d i) o).card:ℝ)≤cost i).trans (paid i)
  intro U cold
  have torus : 2*D i < (R.family.side k per).val :=
    (wide i).trans_le (Nat.le_mul_of_pos_left _ (A.S.period per).pos)
  have coolpos : 0≤cool A k:= by unfold cool RG.Calendar.hatCoupling;positivity
  apply WilsonPhysicalRegisteredLocalAction.admitted J clear o (D i) torus _ _ _ U coolpos cold
    ((width i).trans_lt (half_lt_self positive)) (min_le_left ..) size
  intro e he
  obtain ⟨a,b⟩:=(Finset.mem_filter.mp he).2
  exact ⟨a,b,(reaches R (d i) o e.1 a).trans_lt (by dsimp [D];omega)⟩

/-- The genuine fitted report at all its original stops, using these exact
larger cold cells, together with local chart admission on the same scene. -/
theorem measured (stoves : Poetry R.family.path.levels) (simple : G.Simple) (D : I→ℕ)
    (ℓ : (i:I)→Letter (D i)) (φ : Wave I) (compact : HasCompactSupport φ.val) (s q : ℕ)
    {ε r₀ : ℝ} (ep : 0<ε) (J : Voice G) (clear : Clear G J) (pr : 0<r₀) :
    ∃b:ℝ,0<b ∧ ∀ᶠ k:ℕ in atTop,
      (∀per i (o : Site (R.family.side k per)) U, U∈House.chilly (faces R (kept (ℓ i)) o) (cool R.family.path.levels k)→
        let B:=(R.family.localSection (kept (ℓ i))).footprint o
        let E:=bonds R (kept (ℓ i)) o
        0<(colors G _).real (window B E U b) ∧ ∀z∈window B E U b,
          (fun e:↥E=>Lattice.gauge (change B z) U e.val)∈Chart.chamber G (↥E) r₀) ∧
      ∀N per,k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
      ∀(x:(i:I)→R.family.label (kept (ℓ i))) r ξ,
      let e:=fun i=>kept (ℓ i)
      let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) k N per) (ℓ i)
      let cells:=fun (z:placements (V:=I) R.family k per t) i=>faces R (e i) (z.val i)
      ∀(n u:ℕ)(date:n+1≤k)(span:u≤n)(g:Body),
        (∫V, ‖field R.family N per date span (read R e k N per t y φ r ξ) g V-
          field R.family N per date span (primary R e k N per t y φ r ξ cells) g V‖ ∂scene R.family.path N per u)≤
        (∏i,mass R.family (e i) (x i))*(ε*Pert.Asymptotics.regulatorRun R.family N per k^q) := by
  obtain ⟨b,bpos,admit⟩:=admitted R simple (fun i=>kept (ℓ i)) J clear pr
  refine ⟨b,bpos,?_⟩
  filter_upwards [admit,WilsonPositionSeparatedProfileFittedPrimary.tested R stoves simple D ℓ φ compact 1 s q ep] with k actual issued
  refine ⟨fun per i o=>(actual per i o).2,?_⟩
  intro N per live t rad x r ξ
  apply issued N per live t rad x r ξ _ (fun z i=>covers R (kept (ℓ i)) (z.val i))
  intro z i
  simpa only [pow_one] using (actual per i (z.val i)).1

end YM.Integration.WilsonReportingRegisteredAction
