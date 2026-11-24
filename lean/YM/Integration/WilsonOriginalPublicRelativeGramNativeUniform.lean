import YM.Integration.WilsonOriginalPublicRelativeGramNativePivot

/-! Cutoff-uniform reflected Gram on the actual physical trial mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeUniform
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalPublicRelativeGramPosted (Dated gram)
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered)
open WilsonOriginalPublicRelativeGramNativeSites (sample)
open WilsonOriginalPublicRelativeGramPlanted (file)
open WilsonPositionProgramTrialOpticalBand (Band Bracket)
open scoped Topology Classical

open WilsonOriginalPublicRelativeGramNativePivot (Ruler filed)
open WilsonOriginalPublicPlantedGramFilms (reflected pupil)
open WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicDirectoryCoin
open WilsonPositionProgramPublicWickGram (nodes reading)
open scoped BigOperators

variable {G:Gauge}(R:Run G)(pres:WilsonPrescription G)(B:Deck G)(h:ℕ)(a:Axis)
    (avoid:Finset E4)(L:Ruler R pres.run)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
variable (paper:ℝ → WilsonOriginalPublicRelativeGramPosted.Dated (L:=Unit) R pres.scheme (fun _:Glyph B h=>h))(q:ℕ)
variable {simple:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(verified:Main.Match pres simple M T dial)

/-- All finite physical periods and every ultraviolet cutoff above the nominated top. -/
def above {D:XSpace.Run}(L:Ruler R D):Filter Z:=
  ordered trail (fun r=>Filter.principal {z:ℕ×ℕ | L.top r≤z.1})

include verified paper avoid q in
theorem original {A:ℝ}(ap:0≤A)(cut:Bracket R L.cut A):
    Tendsto (fun p:Z=>WilsonOriginalPublicRelativeGramPosted.gram R pres.scheme (fun _:Glyph B h=>h) (WilsonOriginalPublicRelativeGramNativePivot.filed R pres B h a avoid L q p.1 (paper p.1)) p.2)
      (above R L) (𝓝 (maxwell B h a)):=by
  let money:=WilsonOriginalPublicRelativeGramKineticMesh.thermal R
  obtain ⟨warm,cold,span,actual⟩:=WilsonOriginalPublicRelativeGramKineticMesh.original R simple
    pres.run L.board ap cut L.turn L.cofinal
  let X:=fun r=>sample R avoid (pointsAt a) (pres.run.step (L.mesh r)) (L.live r) (L.scale r) (L.scale r)
  have pose:=WilsonOriginalPublicRelativeGramNativeSites.original R avoid (pointsAt a)
    (fun r=>pres.run.step (L.mesh r)) L.place L.top L.live L.scale L.scale (gain:=1)
    (Eventually.of_forall fun r=>⟨R.family.S.a_pos _,R.family.S.a_pos _,L.gauge r⟩)
    L.fine (by
      apply (tendsto_const_nhds (x:=(1:ℝ))).congr
      intro r
      exact (div_self (R.family.S.a_pos _).ne').symm)
  have locations:Tendsto (fun r=>familiar (X r)) trail (𝓝 (lower a)):=by
    have move:=pose.2
    rw [one_smul] at move
    rw [placement]
    convert move using 1 <;> rfl
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply Metric.tendsto_nhds.mpr
  intro e ep
  obtain ⟨ρ,rp,paid⟩:=WilsonOriginalPublicPlantedShortGram.matrix (L:=Unit) pres verified a
    (id:I→I) trail (Eventually.of_forall warm) cold (e/2) 1 2 (4*A)
    (half_pos ep) (by norm_num) (by norm_num) q
  change ∀ᶠr in trail, ∀ᶠz in Filter.principal {p:ℕ×ℕ | L.top r≤p.1}, _
  filter_upwards [paid,span,actual,Metric.tendsto_nhds.mp locations ρ rp] with r buy dates heat close
  apply eventually_principal.mpr
  intro z live
  let u:=regulatorRun R.family z.1 z.2 (L.top r)
  let μ:Unit→ℂ:=fun _=>1
  let X₀:Unit→Sample 2:=fun _=>X r
  have phase:=buy (L.mesh r) dates.1 dates.2 X₀ μ (fun _=>rfl)
    (fun _=>⟨pose.1 r,close⟩) (by simp [μ]) (by simp [μ]) u (heat z.1 z.2 live)
  let H:=fun (i j:I)=>WilsonOriginalPublicPivotCross.detector pres.scheme X₀ μ q u
    (reflected pres a (L.mesh r) i*pupil pres (L.mesh r) j)
  let M₀:=reading a (nodes a) (id:I→I)
  have charged:‖H-M₀‖≤e/2:=phase
  rw [dist_eq_norm]
  exact ((norm_le_pi_norm ((H-M₀) i) j).trans ((norm_le_pi_norm (H-M₀) i).trans charged)).trans_lt
    (half_lt_self ep)

theorem cofinal {D:XSpace.Run}(L:Ruler R D)(f:Extraction.Order):
    ordered trail (fun _:ℝ=>f.fuse)≤above R L:=by
  intro s received
  change ∀ᶠr in trail,∀ᶠz in f.fuse,(r,z)∈s
  change ∀ᶠr in trail,∀ᶠz in Filter.principal {p:ℕ×ℕ | L.top r≤p.1},(r,z)∈s at received
  filter_upwards [received] with r ready
  have grow:∀ᶠz:ℕ×ℕ in f.fuse,L.top r≤z.1:=by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.monotone.tendsto_atTop.eventually_ge_atTop _
  filter_upwards [grow] with z pos
  exact eventually_principal.mp ready z pos

end YM.Integration.WilsonOriginalPublicRelativeGramNativeUniform
