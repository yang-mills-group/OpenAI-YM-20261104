import YM.Integration.WilsonOriginalPublicRelativeGramReflectedLimit
import YM.Integration.WilsonOriginalPublicRelativeGramPosted

/-! The original N-born self panel, its genuinely submitted compensated
finite programme and all prior deposits determine the one public branch on
the ordered physical extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramBranch
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered entered)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

private theorem recover {Z:Type}{l:Filter Z}(P Q T:Z→ℂ)(fee old:Z→ℝ)(x:ℂ)
    (physical:Tendsto P l (𝓝 x))(recent:Tendsto fee l (𝓝 0))(prior:Tendsto old l (𝓝 0))
    (hearing:∀ᶠ z in l,‖P z-Q z‖≤fee z)(complete:∀z,‖Q z-T z‖≤old z):
    Tendsto T l (𝓝 x):=by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have ep3:0<ε/3:=by positivity
  filter_upwards [Metric.tendsto_nhds.mp physical (ε/3) ep3,
    recent.eventually (gt_mem_nhds ep3),prior.eventually (gt_mem_nhds ep3),hearing] with z near small older tested
  calc
    dist (T z) x ≤ dist (T z) (Q z)+dist (Q z) x:=dist_triangle ..
    _ ≤ old z+(dist (Q z) (P z)+dist (P z) x):=by
      apply add_le_add _ (dist_triangle ..)
      simpa only [dist_comm (T z),dist_eq_norm] using complete z
    _ < ε:=by
      have d:dist (Q z) (P z)≤fee z:=by rw [dist_comm,dist_eq_norm]; exact tested
      linarith only [near,small,older,d]

variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (Y:ℝ→(ℕ×ℕ)→I→R.family.label h)(b:ℝ→I→R.family.label h)
    (selected:∀ᶠr in trail,(∀i,Tendsto (fun z=>Y r z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b r i))) ∧
       ∀i,S.project h (b r i)=J r h (named R B h i))
    (W:Initialize G)(sale:ℝ→Dated (L:=Unit) R W d)(fee:Z→I→I→ℝ)(level:I→ℕ)
    (covered:Tendsto (fun p:Z=>gram R W d (sale p.1) p.2) fused (𝓝 (maxwell B h a)))
    (hearing:∀ i j,∀ᶠp:Z in fused,
      ‖entered B h a R F ℓ avoid Γ Y p i j-submitted R W d (sale p.1) false p.2 i j‖≤fee p i j)
    (fresh:∀ i j,Tendsto (fun p:Z=>fee p i j) fused (𝓝 0))
    (deposited:∀ i j,Tendsto (fun p:Z=>deposits R W d (sale p.1) false p.2 i j) fused (𝓝 0))
    (headers:∀i j,level j≤level i → Tendsto (fun p:Z=>(sale p.1).frame false p.2 i j) fused
      (𝓝 ((1:Matrix I I ℂ) i j))):
    Tendsto (fun p:Z=>(sale p.1).frame false p.2) fused (𝓝 1):=by
  have physical:=WilsonOriginalPublicRelativeGramReflectedLimit.original B h a R F J ℓ avoid Γ
    simple temperature lead below Y b selected
  apply WilsonOriginalPublicRelativeGramOrientationLimit.original B h a _ _ level covered _ headers
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply recover _ _ _ (fun p:Z=>fee p i j) (fun p:Z=>deposits R W d (sale p.1) false p.2 i j) _
    (((continuous_id.matrix_elem i j).tendsto _).comp physical) (fresh i j) (deposited i j) (hearing i j)
  exact fun p=>WilsonOriginalPublicRelativeGramPosted.printed R W d (sale p.1) false p.2 i j

end YM.Integration.WilsonOriginalPublicRelativeGramBranch
