import YM.Integration.WilsonPositionProgramPublicReflectedFund
import YM.Euclid.RPPeak

/-! The physical convention puts the signed, conjugated first source in
the negative half space. Use that order on the actual public mesh. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicReflectedRead
open Function Filter Set Source Labels Maxwell Maxwell.Wick MS MS.Menus MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Retirement
open Local.Physical Extra Extra.FD Table.Pairing
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicContrast
open scoped Topology BigOperators Classical
variable {G:Gauge} {d:ℕ} {I:Type} [Fintype I] {B : Local.Physical.Deck G}
    (W:Initialize G) (V:Normalize.Store G) (a:Axis) (leg:I→Glyph B d)
def center := points (fun _:Fin 1=>vertex a)
def lower := closedUp a (center a) (center a)

theorem positive : 0<vertex a a := by simp [vertex,YM.basis]

theorem reflected : Table.Pairing.ride a (vertex a) = -(vertex a) := by
  ext b
  by_cases h:b=a <;> simp [Table.Pairing.ride,vertex,YM.basis,h]

theorem placement : lower a = FD.couple (-(vertex a)) (vertex a) := by
  ext1 i
  fin_cases i
  · change closedUp a (center a) (center a) (Fin.castAdd 1 (0:Fin 1))=_
    rw [enter]; exact reflected a
  · change closedUp a (center a) (center a) (Fin.natAdd 1 (0:Fin 1))=_
    rw [leave]; rfl

theorem separated : lower a∈conf 2 := by
  apply Table.Pairing.spans <;> exact ⟨fun _ _ _=>Subsingleton.elim _ _,fun _=>positive a⟩

def signed (i j:I) : Tags G d 2 :=
  ![τ (Signed.mirror a) d (Theater.Daylight B d (leg i)),Theater.Daylight B d (leg j)]

omit [Fintype I] in
theorem actual (i j:I) : scene (lower a) d (signed a leg i j)=reading a (nodes a) leg i j := by
  have hx : lower a∈conf 2 := separated a
  let s:=Equiv.swap (0:Fin 2) 1
  have swap : Points.rearrange s (lower a) = nodes a := by
    rw [placement]
    ext1 i
    fin_cases i <;> simp [s] <;> rfl
  rw [screen,reading,screen,exchangeSites s hx]
  change (moment G (Points.rearrange s (lower a))) _ = _
  rw [swap]
  congr 1
  ext1 i
  fin_cases i <;> simp [s] <;> rfl

def matrix (x:Sample 2) (i j:I) : ℂ := cooked W V d x 0 (signed a leg i j)

omit [Fintype I] in
theorem earned : Tendsto (matrix W V a leg) (Gate (lower a)) (𝓝 (reading a (nodes a) leg)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  rw [← actual]
  exact scans0 W V d _ _ (separated a)

theorem original (each:Injective leg) :
    ∃ k δ ρ:ℝ, 0<k ∧ 0<δ ∧ 0<ρ ∧ ∀ᶠ M in Front, ∀ (u:pack 2) (c:Four ℝ), c∈M.Box →
      dist (M.rel u c) (lower a)<ρ → ∀ (p:I→I→ℂ), ‖p-matrix W V a leg ⟨M,u,c⟩‖≤δ →
        ∀ v:I→ℂ, k*‖v‖^2≤‖WilsonPositionProgramPublicContrast.assay v v p‖ := by
  obtain ⟨k,t,hk,ht,cap⟩ := WilsonPositionProgramPublicWickGram.original a leg each
  obtain ⟨ρ,hρ,price⟩ := gate_senses (lower a)
    (Metric.tendsto_nhds.mp (earned W V a leg) (t/2) (half_pos ht))
  refine ⟨k,t/2,ρ,hk,half_pos ht,hρ,?_⟩
  filter_upwards [price] with M due u c hc near p hp
  apply cap
  have mid := due u c hc near
  rw [dist_eq_norm] at mid
  exact (norm_sub_le_norm_sub_add_norm_sub p (matrix W V a leg ⟨M,u,c⟩) _).trans (by linarith)
end YM.Integration.WilsonPositionProgramPublicReflectedRead
