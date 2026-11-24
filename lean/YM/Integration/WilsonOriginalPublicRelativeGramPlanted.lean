import YM.Integration.WilsonOriginalPublicRelativeGramBookedHeads
import YM.Integration.WilsonOriginalPublicPlantedShortGram

/-! The normalized independent basis bank is planted on its own finite gauge
quotient and hearing at each radius. All original regulators use the same
independent marked date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramPlanted
open Filter Function Lattice Wilson RG Source Labels Extraction Extraction.Banks RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus
open WilsonOriginalPublicRelativeGramPosted (Dated gram)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered)
open WilsonOriginalPublicPlantedGramFilms (reflected pupil)
open WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicDirectoryCoin
open WilsonPositionProgramPublicWickGram (nodes reading)
open scoped Topology Classical BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(S₀:WilsonPrescription G)(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
local notation "I" => Glyph B h
local notation "d" => (fun _:I=>h)
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "Ticket" => Dated (L:=Unit) R S₀.scheme d

def file (sale:Ticket)(q j:ℕ):Ticket:=
  {sale with q:=q,leftBasis:=fun _ i=>reflected S₀ a j i,rightBasis:=fun _ i=>pupil S₀ j i}

variable (ℓ:Ultrafilter (ℕ×ℕ))(sale:ℝ → Dated (L:=Unit) R S₀.scheme (fun _:Glyph B h=>h))(q:ℕ)(j:ℝ→ℕ)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

local notation "X" p:max => (sale (p:Z).1).nodes p.2 ()
variable {simple:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(match₀:Main.Match S₀ simple M T dial)

include match₀ in
theorem original {t:ℝ→ℝ}(positive:∀ᶠr in trail,0<t r)(small:Tendsto t trail (𝓝 0))
    (lo hi:ℝ)(lp:0<lo)(band:∀ᶠr in trail,
      lo*(-Real.log (t r))≤ -Real.log (S₀.run.step (j r)).spacing ∧
      -Real.log (S₀.run.step (j r)).spacing≤hi*(-Real.log (t r)))
    (near:Tendsto (fun p:Z=>familiar (X p)) fused (𝓝 (lower a)))
    (samples:∀ᶠ p:Z in fused,(X p).F=S₀.run.step (j p.1) ∧ welcome (X p) ∧
      (sale p.1).mass p.2 ()=1 ∧ |(sale p.1).g p.2|≤8*t p.1):
    Tendsto (fun p:Z=>gram R S₀.scheme d (file S₀ B h a R (sale p.1) q (j p.1)) p.2)
      fused (𝓝 (maxwell B h a)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro k
  apply Metric.tendsto_nhds.mpr
  intro e ep
  obtain ⟨ρ,wp,fee⟩:=WilsonOriginalPublicPlantedShortGram.matrix (L:=Unit) S₀ match₀ a
    (id:I→I) trail positive small (e/2) 1 lo hi (half_pos ep) (by norm_num) lp q
  have closeNodes:∀ᶠr in trail,∀ᶠz:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),
      dist (familiar ((sale r).nodes z ())) (lower a)<ρ:=Metric.tendsto_nhds.mp near ρ wp
  change ∀ᶠr in trail,∀ᶠz:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),_ at samples ⊢
  filter_upwards [fee,band,samples,closeNodes] with r registered span board locations
  filter_upwards [board,locations] with z ready close
  let p:Z:=(r,z)
  let X₀:Unit→Sample 2:=(sale p.1).nodes p.2
  let μ:Unit→ℂ:=(sale p.1).mass p.2
  have mass:∑u,μ u=1:=by simpa only [Fintype.sum_unique] using ready.2.2.1
  have total:∑u,‖μ u‖≤1:=by simp only [Fintype.sum_unique];rw [show μ default=1 from ready.2.2.1,norm_one]
  have phase:=registered (j p.1) span.1 span.2 X₀ μ (fun _=>ready.1)
    (fun _=>⟨ready.2.1,close⟩) mass total _ ready.2.2.2
  let A:=fun (v w:I)=>WilsonOriginalPublicPivotCross.detector S₀.scheme X₀ μ q ((sale p.1).g p.2)
    (reflected S₀ a (j p.1) v*pupil S₀ (j p.1) w)
  let M₀:=reading a (nodes a) (id:I→I)
  have charged:‖A-M₀‖≤e/2:=phase
  rw [dist_eq_norm]
  exact ((norm_le_pi_norm ((A-M₀) i) k).trans ((norm_le_pi_norm (A-M₀) i).trans charged)).trans_lt
    (half_lt_self ep)

end YM.Integration.WilsonOriginalPublicRelativeGramPlanted
