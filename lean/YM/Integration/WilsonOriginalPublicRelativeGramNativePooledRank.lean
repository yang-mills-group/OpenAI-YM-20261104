import YM.Integration.WilsonOriginalPublicRelativeGramNativeDiagonal

/-! The physical reflected charge pays the whole compensated vector at finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativePooledRank
open Filter Set Function Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(B:Deck G)(d:ℕ)(a:Axis)
local notation "I" => Glyph B d
local notation "Frame" => Matrix I I ℂ

/-- The scale can depend on the physical date and on both physical regulators. -/
def Accepts (C:ℝ):Prop:=∀{Z:Type}{l:Filter Z}(A H:Z → Frame)(w:Z → ℝ)
    (u e t:Z → I → ℝ),Tendsto H l (𝓝 (maxwell B d a)) →
    (∀ᶠz in l,1≤w z ∧ ∀j:I,0≤u z j ∧ e z j*u z j≤1 ∧ e z j*(u z j)^2≤1 ∧ t z j≤1 ∧
      ‖((A z)ᴴ*H z*A z) j j‖≤(w z)^2+1+
        e z j*(2*u z j*‖fun i:I=>A z i j‖+(u z j)^2)+t z j) →
    ∀ᶠz in l,‖A z‖≤C*w z

theorem original:∃C:ℝ,0<C ∧ Accepts B d a C:=by
  obtain ⟨k,δ,kp,dp,rank⟩:=WilsonPositionProgramPublicWickGram.original a (id:I→I) injective_id
  let cap:=max 1 (((1:ℝ)+5)/k)
  let C:=max 1 (∑_i:I,∑_j:I,cap)
  refine ⟨C,zero_lt_one.trans_le (le_max_left ..),?_⟩
  intro Z l A H w u e t cover paid
  let G₀:=WilsonPositionProgramPublicWickGram.reading a (WilsonPositionProgramPublicWickGram.nodes a) (id:I → I)
  let table:=fun z i j=>H z i j
  have atlas:Tendsto table l (𝓝 G₀):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact ((continuous_id.matrix_elem i j).tendsto _).comp cover
  filter_upwards [Metric.tendsto_nhds.mp atlas δ dp,paid] with z close money
  calc
    ‖A z‖≤∑_i:I,∑_j:I,cap*w z:=by
      apply WilsonOriginalPublicRelativeGramPanel.entry_bound (fun _ _=>cap*w z)
      intro i j
      let x:I→ℂ:=fun n=>A z n j
      have invoice:=money.2 j
      have finite:‖table z-G₀‖≤δ:=by simpa only [←dist_eq_norm] using close.le
      have earn:=rank (table z) finite x
      change k*‖x‖^2≤‖assay x x (H z)‖ at earn
      rw [show assay x x (H z)=_ from WilsonOriginalPublicRelativeGramPrint.entry (A z) (H z) (A z) j j] at earn
      have hearing:=earn.trans invoice.2.2.2.2
      have amount:=WilsonOriginalPublicPivotReflected.absorption kp (norm_nonneg x) invoice.1
        money.1 (zero_le_one:0≤(1:ℝ)) invoice.2.1 invoice.2.2.1 invoice.2.2.2.1
        (by simpa only [one_mul] using hearing)
      exact (norm_le_pi_norm x i).trans amount
    _=(∑_i:I,∑_j:I,cap)*w z:=by simp only [Finset.sum_mul]
    _≤C*w z:=mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans money.1)

end YM.Integration.WilsonOriginalPublicRelativeGramNativePooledRank
