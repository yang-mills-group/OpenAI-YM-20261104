import YM.Integration.WilsonMaxwellThermometerIncidenceSmearing
import YM.Integration.WilsonMaxwellThermometerCommonTangent

/-! Signed first-frame displacement of the full regulated thermometer. Its
three terms are tested at the same finite W site and the same original Rose
cell mass. All lower-grade and unit polynomials remain in the input. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFiniteTangent
open Filter Set Finset Function Metric MeasureTheory Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement XSpace.Graph3
open WilsonMaxwellThermometerBareIncidenceRate (assembled)
open WilsonMaxwellThermometerIncidenceSmearing (integrated)
open WilsonMaxwellThermometerCommonTangent (payout Equivariant)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G){V:Store G}(K:Pick V)
variable {I:Type} [Fintype I] (B:Module.Basis I ℂ (Sec G 6))

def roster (u:Sec G 6)(p q:Sec G 4):Tags G 6 3:=
  trip u (up (by decide:4≤6) p) (up (by decide:4≤6) q)

def cost (a:Tags G 6 3):ℝ:=∏j,∑i:I,‖(B.repr (a j)) i‖

def credit (M:Mesh)(u:Sec G 6)(p q:Sec G 4):ℂ:=
  integrated W (Rose.test K) M (roster u p q)

theorem full :
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀(u:Sec G 6)(p q:Sec G 4),
      ‖credit W K M u p q-payout K u p q‖≤C*M.spacing*cost B (roster u p q):=by
  obtain ⟨C,hC,fee⟩:=WilsonMaxwellThermometerIncidenceSmearing.original W (Rose.test K)
    (I:=fun _:Fin 3=>I) (fun _ i=>B i)
  let V₀:=∫x:Points 3,‖Rose.test K x‖
  have V_pos:0≤V₀:=integral_nonneg (fun x=>norm_nonneg _)
  refine ⟨V₀*C,mul_nonneg V_pos hC,?_⟩
  filter_upwards [fee] with M paid
  intro u p q
  let f:=roster u p q
  let a (j:Fin 3)(i:I):ℂ:=(B.repr (f j)) i
  have eq:assembled 6 (fun (_:Fin 3)i=>B i) a=f:=by
    funext j;exact B.sum_repr _
  change ‖integrated W (test K) M f-(test K).applyTo (fun x=>
    WilsonMaxwellThermometerFaces.connected x f)‖≤
    ((∫x:Points 3,‖test K x‖)*C*M.spacing)*∏j,∑i,‖a j i‖
  simpa only [eq] using paid a

def change (M:Mesh)(u du:Sec G 6)(p dp q dq:Sec G 4):ℂ:=
  credit W K M du p q + credit W K M u dp q + credit W K M u p dq

def fare (u du:Sec G 6)(p dp q dq:Sec G 4):ℝ:=
  cost B (roster du p q)+cost B (roster u dp q)+cost B (roster u p dq)

/-- The complete finite first response from the actual common change on the
three slots. The signed leading odd component and any even mixture are
permitted on the upper leg. No reflection parity is assumed for it. -/
theorem original (simple:G.Simple):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀(u du:Sec G 6)(P dP Q dQ:Module.End ℂ (Sec G 4)),
    Equivariant P→Equivariant dP→Equivariant Q→Equivariant dQ→
    let b:=lower G
    ‖change W K M u du (P b) (dP b) (Q b) (dQ b)‖≤
      C*M.spacing*fare B u du (P b) (dP b) (Q b) (dQ b):=by
  obtain ⟨C,hC,fee⟩:=full W K B
  refine ⟨C,hC,?_⟩
  filter_upwards [fee] with M paid
  intro u du P dP Q dQ hP hdP hQ hdQ
  let b:=lower G
  have a:=paid du (P b) (Q b)
  have d:=paid u (dP b) (Q b)
  have e:=paid u (P b) (dQ b)
  rw [WilsonMaxwellThermometerCommonTangent.separate K simple du P Q hP hQ,sub_zero] at a
  rw [WilsonMaxwellThermometerCommonTangent.separate K simple u dP Q hdP hQ,sub_zero] at d
  rw [WilsonMaxwellThermometerCommonTangent.separate K simple u P dQ hP hdQ,sub_zero] at e
  let a₀:=cost B (roster du (P b) (Q b))
  let a₁:=cost B (roster u (dP b) (Q b))
  let a₂:=cost B (roster u (P b) (dQ b))
  change ‖credit W K M du (P b) (Q b)+credit W K M u (dP b) (Q b)+credit W K M u (P b) (dQ b)‖
    ≤C*M.spacing*(a₀+a₁+a₂)
  rw [mul_add,mul_add]
  apply (norm_add_le ..).trans
  exact add_le_add ((norm_add_le ..).trans (add_le_add a d)) e

end YM.Integration.WilsonMaxwellThermometerFiniteTangent
