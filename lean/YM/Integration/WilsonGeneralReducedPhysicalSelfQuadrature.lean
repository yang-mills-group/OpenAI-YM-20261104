import YM.Integration.WilsonGeneralReducedPhysicalSelfGappedBoard
import YM.Integration.WilsonGeneralReducedPhysicalSelfThermal

/-! The actual cell partition of a smooth, normalized test on the compact
determining packet. All occupied cell weights are positive, sum to one and
apply to every deposited vector on the same finite board. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfQuadrature
open Set Filter Function Finset MeasureTheory Metric Lattice XSpace XSpace.Rose XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register MS MS.Land MS.Menus Local.Physical
open WilsonGeneralReducedPhysicalSelfGappedBoard (atPlace)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open private oneSite from YM.Integration.WilsonGeneralReducedPhysicalSelfThermal
open private placed from YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure
open scoped Classical Topology BigOperators
variable (M:Mesh)(c:Four ℝ){p:Points 2}(b:ContDiffBump p)
local notation "Sites" => Fin 2→M.Sites
def seat (y:Points 2):Sites:=chartV (atPlace M c y)
def cell (s:Sites):Set (Points 2):={y|seat M c y=s}

theorem legal (s:Sites):MeasurableSet (cell M c s):=by
  let E:Set (pack 2):={o|chartV (⟨M,o,c⟩:Sample 2)=s}
  change MeasurableSet ((fun y:Points 2=>draw y M c) ⁻¹' E)
  apply (show Measurable (fun y:Points 2=>draw y M c) from ?_) (E.to_countable.measurableSet)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply Int.measurable_ceil.comp
  change Measurable (fun y:Points 2=>(y+Mesh.room c : Points 2) i j / M.spacing)
  fun_prop

def weight (s:Sites):ℝ:=∫y:Points 2,(cell M c s).indicator (b.normed volume) y
def contact (s:Sites):Prop:=∃y∈tsupport b,seat M c y=s
def representative (s:Sites):Points 2:=if paid:contact M c b s then paid.choose else p

private theorem active {y:Points 2}(hit:b.normed volume y≠0):y∈tsupport b:=by
  have member:y∈Function.support (b.normed volume):=hit
  rw [b.support_normed_eq] at member
  rw [b.tsupport_eq]
  exact ball_subset_closedBall member

theorem inside (s:Sites):representative M c b s∈tsupport b:=by
  unfold representative
  split
  next h=>exact h.choose_spec.1
  next=>rw [b.tsupport_eq];exact mem_closedBall_self b.rOut_pos.le

theorem positive (s:Sites):0≤weight M c b s:=by
  apply integral_nonneg
  intro y
  exact indicator_nonneg (fun y _=>b.nonneg_normed y) _

theorem total :∑s:Sites,weight M c b s=1:=by
  unfold weight
  rw [←integral_finsetSum _ (fun s _=>b.integrable_normed.indicator (legal M c s))]
  suffices (fun y:Points 2=>∑s:Sites,(cell M c s).indicator (b.normed volume) y)=b.normed volume by
    rw [this,b.integral_normed]
  funext y
  simp [cell,Set.indicator_apply]

private theorem clean (s:Sites)(hit:weight M c b s≠0):seat M c (representative M c b s)=s:=by
  by_cases h:contact M c b s
  · simpa [representative,h] using h.choose_spec.2
  · exfalso
    apply hit
    rw [weight]
    have cancel:(cell M c s).indicator (b.normed volume)=0:=by
      funext y
      by_cases inCell:y∈cell M c s
      · rw [indicator_of_mem inCell]
        by_contra dirty
        exact h ⟨y,active b dirty,inCell⟩
      · exact indicator_of_notMem inCell _
    rw [cancel]
    simp

theorem evaluate (f:Sites→ℂ):
    (∫y:Points 2,b.normed volume y • f (seat M c y))=
      ∑s:Sites,weight M c b s • f (seat M c (representative M c b s)):=by
  have split (y:Points 2):b.normed volume y • f (seat M c y)=
      ∑s:Sites,((cell M c s).indicator (b.normed volume) y) • f s:=by
    simp [cell,Set.indicator_apply,ite_smul]
  simp_rw [split]
  rw [integral_finsetSum _ (fun s _=>(b.integrable_normed.indicator (legal M c s)).smul_const _)]
  apply sum_congr rfl
  intro s _
  rw [integral_smul_const]
  by_cases hs:weight M c b s=0
  · change weight M c b s • _=weight M c b s • _
    simp [hs]
  · rw [clean M c b s hs]
    rfl

variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis){h:ℕ}{B:Deck G}
theorem original (j q:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(room:Handoff.Directory.budget G 2 h+q≤cap)
    (u:ℝ)(v:Glyph B h→ℂ):
    let F:=Z.run.step j
    let read:=fun y=>cash q u (finiteWord Z a j (atPlace F c y) v)
    (∫y:Points 2,b.normed volume y • read y)=
      ∑s:Fin 2→F.Sites,weight F c b s • read (representative F c b s):=by
  let F:=Z.run.step j
  let value:=fun s:Fin 2→F.Sites=>cash q u (finiteWord Z a j (placed F c s) v)
  have same(y:Points 2):cash q u (finiteWord Z a j (atPlace F c y) v)=value (seat F c y):=
    oneSite Z a j q P (atPlace F c y) v u rfl room
  let read:=fun y=>cash q u (finiteWord Z a j (atPlace F c y) v)
  change (∫ y:Points 2,b.normed volume y • read y)=∑s:Fin 2→F.Sites,weight F c b s • read (representative F c b s)
  have eq : read=fun y=>value (seat F c y):=funext same
  rw [eq]
  exact evaluate F c b value

end YM.Integration.WilsonGeneralReducedPhysicalSelfQuadrature
