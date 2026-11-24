import YM.FVAAlt2.Repop.Singer
/-!
# Actually prepared W. Mark amplitudes (single.H may itself be a full list). No post hoc horizon costs introduced to reader. Segments start from genuinely invested coefficient basis.Temporal serialization. Does not require/pretend Gram fields admission.
 Choosing W after receipts in Epoch matching the given through orders. The *datum* selected per query-family A THROUGH r: can select all such r _before_ making the coefficient queries. No assertion existence of a single analytic W beyond all orders at fixed Step. They match up through any such r and in particular may answer all orders separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Repop
open RG Wilson Tree Exterior Lattice Precision MeasureTheory
open Comparison.RG02 Symmetry Symmetry.Orbit Comparison.RG02.Moving Moving.Path Moving.Shift Valence Assembly Adjacent Bulk
open Filter Function Set Finset Push.SectorMeasure Gauge Integral ConnectedActivityE6 Matrix
open PertExtension.Series PertExtension.Series.Tested
open Diagram Diagram.Formal Binding Booth Booth.Uniforms Prim PowerSeries Marker Multi
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{n:Side}{q: RG.Clip}{P: PathData G}{R: Type}[DecidableEq R]
variable (K:Census R)
variable (V W:Orders (Pin n G)) (C:UnitCost)(u:R)(r m:ℕ)
variable (h: Bright V P q r)(H: Glyph W r m)
local notation "M"=> Multi.Hot K
local notation "σ"=> Uniforms.cuff W m
local notation "X"=> fieldDir G n 1

def layout (χ:Chi)(δ:ℝ)(q:RG.Clip)(P:PathData G): Bulk.Colors K G n where
  vac:= singer C q P V r χ δ
  mark i:= if i= (Arm.pub u : Multi.Hot K) then garment C (Uniforms.cuff W m) r m χ δ else 0
  power _:=m
variable (χ:Chi){δ γ:ℝ}(hv: Reliable G δ γ)
variable {b α η:ℝ}(hp:P.Bounds q b α η)
local notation "D"=> layout K V W C u r m χ δ q P
local notation "E"=> Arm.pub (R:=K) u
include h H hp hv
lemma proper : Well D:= by
    refine { suppose_vac:= readyChart C q P V r h χ hv hp, natural:= wearing C q P V r h χ hv hp, envelope:=pose C q P V r h χ hv hp,suppose_mark:= ?_, gauges:= ?_, prices:=?_ }
    · intro i; by_cases hx:i= E
      · dsimp only [layout]; rw [if_pos hx]; exact warm C (cuff W m) r m H.sheet H.valid hv χ
      dsimp only [layout]; rw [if_neg hx]; exact GradeAt.grade_zero m
    · intro i s; by_cases hx:i= E; · dsimp only [layout]; rw [if_pos hx]; exact gauged C (cuff W m) r m H.sheet H.valid hv χ s
      dsimp only [layout]; rw [if_neg hx]; exact fun _ _=>rfl
    intro i s; by_cases hx:i= E; · dsimp only [layout]; rw [if_pos hx]; exact Envelope.compactC (earned_c C _ r m H.sheet H.valid hv χ s)
    dsimp only [layout]; rw [if_neg hx]; exact Envelope.constC 0
lemma minds : Arm.Simmer q P C (layout K V W C u r m χ δ q P) V r:= ⟨proper K V W C u r m h H χ hv hp, h.paid,h.paved,bearing C q P V r h χ hv hp D rfl⟩ -- Simmer namespace
lemma knowing : Arm.Single C D W u r m := by
    refine ⟨ H.paved,H.grade,?_ ⟩; intro e he x
    change motion (Arm.shineM C D u x) (m+e)= ( ↑(coeff e ( flavor m (FreeResolvent.flatten x) W )) : ℂ )
    unfold Arm.shineM; simp_rw [ show ( D ).mark E= _ from (show (D).mark (Arm.pub u)= garment C (cuff W m) r m χ δ from if_pos rfl) ]; exact entered C (cuff W m) r m H.sheet H.valid hv χ x e he
omit hv
include hp
lemma obtainT : ∃ Mᵦ:Bulk.Colors K G n, Arm.Simmer q P C Mᵦ V r ∧ Arm.Single C Mᵦ W u r m ∧ Mᵦ.power (Arm.pub u)=m:=by
   obtain ⟨g,z,hz,hv⟩:= ConnectedActivityE6.reliable G; exact ⟨_, minds K V W C u r m h H Chi.canonical (hv z hz le_rfl) hp, knowing K V W C u r m h H Chi.canonical (hv z hz le_rfl) hp, rfl⟩

end YM.RegulatorIR.FVAAlt2.Repop
