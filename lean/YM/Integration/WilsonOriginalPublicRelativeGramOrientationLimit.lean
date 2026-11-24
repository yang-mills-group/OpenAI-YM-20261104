import YM.Integration.WilsonOriginalPublicRelativeGramOriented
import YM.Integration.WilsonOriginalPublicRelativeGramPrint

/-! Oriented limits of the complete normalized numerical public frames. The
original reflected self-readings bound every column before compactness. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOrientationLimit
open Filter Finset Function Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {I Z:Type}[Fintype I][DecidableEq I]{l:Filter Z}
local notation "Mat" => Matrix I I ℂ

omit [Fintype I] [DecidableEq I] in
private theorem entry {A:Z→Mat}{Q:Mat}(cv:Tendsto A l (𝓝 Q))(i j:I):
    Tendsto (fun z=>A z i j) l (𝓝 (Q i j)):=
  ((continuous_id.matrix_elem i j).tendsto Q).comp cv

theorem determined (A H:Z→Mat)(M:Mat)(grade:I→ℕ)(C:ℝ)
    (bounded:∀ᶠz in l,‖A z‖≤C)(cv:Tendsto H l (𝓝 M))
    (heard:Tendsto (fun z=>(A z)ᴴ*(H z)*(A z)) l (𝓝 M))
    (positive:∀x:I→ℂ,assay x x M=0 → x=0)
    (headers:∀ i j,grade j≤grade i → Tendsto (fun z=>A z i j) l (𝓝 ((1:Mat) i j))):
    Tendsto A l (𝓝 1):=by
  apply (isCompact_closedBall (0:Mat) C).tendsto_nhds_of_unique_mapClusterPt
  · exact bounded.mono fun _ b=>by simpa only [Metric.mem_closedBall,dist_zero_right] using b
  intro X _ cluster
  have nonempty:NeBot (𝓝 X ⊓ map A l):=cluster
  rw [←Filter.push_pull',Filter.map_neBot_iff] at nonempty
  let top:=comap A (𝓝 X) ⊓ l
  letI : NeBot top:=nonempty
  have atX:Tendsto A top (𝓝 X):=tendsto_comap.mono_left inf_le_left
  have common:top≤l:=inf_le_right
  have adj:Tendsto (fun z=>(A z)ᴴ) top (𝓝 Xᴴ):=
    (continuous_id.matrix_conjTranspose.tendsto X).comp atX
  have square:=tendsto_nhds_unique ((adj.mul (cv.mono_left common)).mul atX) (heard.mono_left common)
  apply WilsonOriginalPublicRelativeGramOriented.determined grade M X positive square
  intro i j order
  exact tendsto_nhds_unique (entry atX i j) ((headers i j order).mono_left common)

variable {G:Gauge}(B:Local.Physical.Deck G)(d:ℕ)(a:Axis)
local notation "Label" => Glyph B d
local notation "Frame" => Matrix Label Label ℂ

theorem bounded (A H:Z→Frame)
    (cv:Tendsto H l (𝓝 (maxwell B d a)))
    (heard:Tendsto (fun z=>(A z)ᴴ*(H z)*(A z)) l (𝓝 (maxwell B d a))):
    ∃C:ℝ,∀ᶠ z in l,‖A z‖≤C:=by
  let M:=maxwell B d a
  obtain ⟨k,δ,kp,dp,strong⟩:=WilsonPositionProgramPublicWickGram.original a (id:Label→Label) injective_id
  let jcol (j:Label):ℝ:=1+(1+‖M j j‖)/k
  refine ⟨∑_i:Label,∑j,jcol j,?_⟩
  let table (z:Z):Label→Label→ℂ:=fun i j=>H z i j
  let natGram:Label→Label→ℂ:=WilsonPositionProgramPublicWickGram.reading a
    (WilsonPositionProgramPublicWickGram.nodes a) id
  have tab:Tendsto table l (𝓝 natGram):=by
    apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; exact entry cv i j
  have diag:∀ᶠ z in l,∀j:Label,‖((A z)ᴴ*(H z)*(A z)) j j‖≤1+‖M j j‖:=by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [Metric.tendsto_nhds.mp (entry heard j j) 1 zero_lt_one] with z close
    calc
      _=dist (((A z)ᴴ*(H z)*(A z)) j j) 0:=(dist_zero_right _).symm
      _≤dist (((A z)ᴴ*(H z)*(A z)) j j) (M j j)+dist (M j j) 0:=dist_triangle .. 
      _≤_:=by rw [dist_zero_right]; exact add_le_add_left close.le _
  filter_upwards [Metric.tendsto_nhds.mp tab δ dp,diag] with z close face
  have same:‖table z-natGram‖≤δ:=by
    rw [←dist_eq_norm]
    exact close.le
  have sep:=strong (table z) same
  apply WilsonOriginalPublicRelativeGramPanel.entry_bound (fun _ j=>jcol j)
  intro i j
  let x:Label→ℂ:=fun n=>A z n j
  have upper:k*‖x‖^2≤1+‖M j j‖:=(sep x).trans (by
    rw [show assay x x (H z)=_ from WilsonOriginalPublicRelativeGramPrint.entry (A z) (H z) (A z) j j]
    exact face j)
  have char:‖x‖^2≤(1+‖M j j‖)/k:=(le_div_iff₀ kp).mpr (by linarith only [upper])
  apply (norm_le_pi_norm x i).trans
  dsimp [jcol]
  nlinarith [sq_nonneg (‖x‖-1/2)]

theorem original (A H:Z→Frame)(grade:Label→ℕ)
    (cv:Tendsto H l (𝓝 (maxwell B d a)))
    (heard:Tendsto (fun z=>(A z)ᴴ*(H z)*(A z)) l (𝓝 (maxwell B d a)))
    (headers:∀ i j,grade j≤grade i → Tendsto (fun z=>A z i j) l (𝓝 ((1:Frame) i j))):
    Tendsto A l (𝓝 1):=by
  obtain ⟨C,whole⟩:=bounded B d a A H cv heard
  let M:=maxwell B d a
  obtain ⟨k,δ,kp,dp,strong⟩:=WilsonPositionProgramPublicWickGram.original a (id:Label→Label) injective_id
  have pos:=strong M (by simp only [M,maxwell,sub_self,norm_zero]; exact dp.le)
  apply determined A H M grade C whole cv heard _ headers
  intro x zero
  by_contra non
  have price:=pos x
  rw [zero,norm_zero] at price
  exact (not_lt_of_ge price) (mul_pos kp (pow_pos (norm_pos_iff.mpr non) _))

end YM.Integration.WilsonOriginalPublicRelativeGramOrientationLimit
