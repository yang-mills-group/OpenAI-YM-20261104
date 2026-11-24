import YM.Integration.WilsonOriginalPublicRelativeGramNativeCeiling

/-! Reflected diagonal absorption prices a whole compensated matrix using
the native positive free Gram while a mixed remainder still contains its
unknown column norm. The ceiling precedes every finite programme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeDiagonal
open Filter Set Function Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(B:Deck G)(d:ℕ)(a:Axis)
local notation "I" => Glyph B d
local notation "Frame" => Matrix I I ℂ

def Suffices (C:ℝ):Prop:=∀{Z:Type}{l:Filter Z}(A H:Z → Frame)
    (u e t:Z → I → ℝ),Tendsto H l (𝓝 (maxwell B d a)) →
    (∀ᶠz in l,∀j:Glyph B d,0≤u z j ∧ e z j*u z j≤1 ∧ e z j*(u z j)^2≤1 ∧ t z j≤1 ∧
      ‖((A z)ᴴ*H z*A z) j j‖≤(1+‖maxwell B d a j j‖)+1+
      e z j*(2*u z j*‖fun i:Glyph B d=>A z i j‖+(u z j)^2)+t z j) →
    ∀ᶠz in l,‖A z‖≤C

theorem original:∃C:ℝ,0<C ∧ Suffices B d a C:=by
  let M:=maxwell B d a
  obtain ⟨k,δ,kp,dp,rank⟩:=WilsonPositionProgramPublicWickGram.original a (id:I → I) injective_id
  let rate: I → ℝ:=fun j=>1+‖M j j‖
  let cap: I → ℝ:=fun j=>max 1 ((rate j+5)/k)
  let C:=max 1 (∑_i:I,∑j:I,cap j)
  refine ⟨C,zero_lt_one.trans_le (le_max_left ..),?_⟩
  intro Z l A H u e t cover paid
  let G₀:=WilsonPositionProgramPublicWickGram.reading a (WilsonPositionProgramPublicWickGram.nodes a) (id:I → I)
  let table:=fun z i j=>H z i j
  have atlas:Tendsto table l (𝓝 G₀):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact ((continuous_id.matrix_elem i j).tendsto _).comp cover
  filter_upwards [Metric.tendsto_nhds.mp atlas δ dp,paid] with z close money
  apply (WilsonOriginalPublicRelativeGramPanel.entry_bound (fun _ j=>cap j) ?_).trans (le_max_right ..)
  intro i j
  let x:I → ℂ:=fun n=>A z n j
  have invoice:=money j
  have limit: k*‖x‖^2≤rate j*(1:ℝ)^2+1+e z j*(2*u z j*‖x‖+(u z j)^2)+t z j:=by
    have finite:‖table z-G₀‖≤δ:=by simpa only [←dist_eq_norm] using close.le
    have earn:=rank (table z) finite x
    change k*‖x‖^2≤‖assay x x (H z)‖ at earn
    rw [show assay x x (H z)=_ from WilsonOriginalPublicRelativeGramPrint.entry (A z) (H z) (A z) j j] at earn
    simpa only [one_pow,mul_one] using earn.trans invoice.2.2.2.2
  have rp:0≤rate j:=add_nonneg zero_le_one (norm_nonneg _)
  have amount:=WilsonOriginalPublicPivotReflected.absorption kp (norm_nonneg x) invoice.1
    (le_refl (1:ℝ)) rp invoice.2.1 invoice.2.2.1 invoice.2.2.2.1 limit
  exact (norm_le_pi_norm x i).trans (by simpa only [mul_one] using amount)

end YM.Integration.WilsonOriginalPublicRelativeGramNativeDiagonal
