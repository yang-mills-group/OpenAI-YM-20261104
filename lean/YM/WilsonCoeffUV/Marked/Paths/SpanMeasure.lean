import YM.WilsonCoeffUV.Marked.Capture.JointMeasures
/-!
# Address distributions for all marker arities. Emit once at declared
 powers and with full ROOT cylinder. Regular finite measures (cost before
 any quotient). No claims needed for this law about interacting transport.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Express
open Function Set Filter MeasureTheory Embroider Embroider.Canvas
open scoped Topology ContDiff BigOperators CompactlySupported
variable {ι:Type}{D:ι→ℕ}{J S: Finset ι}
-- Alias the already-produced FB address proposition; specialize to continuous
-- volume axes for unmasked Comet. Don't instantiate any second MeasurableSpace.
abbrev Sky (D:ι→ℕ):= Address.Post D
open Address

def mica (A:Case D)(J:Finset ι)(y:Sky D) := positiveP y.1 * folio A J y.2
lemma slippery (A:(i:ι)→ Scroll (D i))(J:Finset ι)(y:Sky D): mica (fun i=> page (D i) (A i)) J y= positiveP y.1 *∏ i∈ J, crease (A i) (y.2 i).1.2 (y.2 i).2.val:=rfl

def Awe (p:Pen D J)(A:Measure (Sky D)): Prop:= A.Regular ∧ IsFiniteMeasure A ∧ A.real univ=‖p‖ ∧ ∀ v:Case D,touch v J p=∫ y, mica v J y ∂A
lemma showers (p:Pen D J): ∃ A,Awe p A:=by
    let _ : Nonempty (Plot D):=⟨fun i => (⟨0,fun _=>0⟩,zeroC)⟩
    obtain ⟨μ,h,g,x,f⟩:= Address.mixSigned _ p; exact ⟨μ,h,g,x,fun T=> f (seaMark T J)⟩
end YM.WilsonCoeffUV.Wheel.Express
