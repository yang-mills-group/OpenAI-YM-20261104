import YM.MSbar.Heath.Charts

/-! A compact, exactly gauge-invariant representative for a localized
Wilson diagnostic. Transport to a single base point before taking the
remaining compact colour average. The support includes the actual transport
paths; no hypothesis about all raw links being small is made. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAnchoredGauge
open Function Filter Set MeasureTheory Lattice RG Wilson Tree
open scoped Classical Topology
variable {G : Gauge} {n : Side}

structure Roads (n : Side) where
  root : Site n
  arm : Site n→Walk
  closed (x : Site n) : stop x (arm x)=root

def transport (A : Roads n) (U : Config G n) (x : Site n) : G.El := (travel U x (A.arm x))⁻¹
def based (A : Roads n) (U : Config G n) : Config G n := Lattice.gauge (transport A U) U
def rotate (h : G.El) (U : Config G n) : Config G n := Lattice.gauge (fun _=>h) U

theorem covariance (A : Roads n) (l : Site n→G.El) (U : Config G n) :
    based A (Lattice.gauge l U)=rotate (l A.root) (based A U) := by
  have trans (x : Site n) : transport A (Lattice.gauge l U) x=l A.root * transport A U x * (l x)⁻¹ := by
    unfold transport;rw [travel_gauge,A.closed];group
  funext e
  change transport A (Lattice.gauge l U) e.1 * (l e.1 * U e * (l (e.1+step e.2))⁻¹) *
    (transport A (Lattice.gauge l U) (e.1+step e.2))⁻¹ = _
  rw [trans,trans]
  unfold rotate based Lattice.gauge
  group

theorem turns (h k:G.El) (U:Config G n): rotate h (rotate k U)=rotate (h*k) U := by
  funext e;unfold rotate Lattice.gauge;group

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def representative (A : Roads n) (B : Config G n→E) (U : Config G n) : E :=
    ∫ h : G.El,B (rotate h (based A U)) ∂G.probHaar

omit [CompleteSpace E] in
theorem invariant (A : Roads n) (B : Config G n→E) : GaugeInvariant (representative A B) := by
  intro l U
  unfold representative
  simp_rw [covariance,turns]
  exact (measurePreserving_mul_right G.probHaar (l A.root)).integral_comp
    (Homeomorph.mulRight (l A.root)).measurableEmbedding (fun h=>B (rotate h (based A U)))

theorem on_chart (A : Roads n) (B : Config G n→E) (U : Config G n) (y:E)
    (h : ∀k : G.El,B (rotate k (based A U))=y) : representative A B U=y := by
  unfold representative
  simp only [h,integral_const,probReal_univ,one_smul]

theorem physical (A : Roads n) (B : Config G n→E) (h : GaugeInvariant B) : representative A B=B := by
  funext U
  apply on_chart
  intro k
  exact (h _ _).trans (h _ _)

def collar (A:Roads n) (X:Set (Site n)) : Set (Site n) :=
  X ∪ {y | ∃x∈X,y∈visits x (A.arm x)}

omit [CompleteSpace E] in
theorem support (A : Roads n) {B : Config G n→E} {X:Set (Site n)} (h:LocalOn X B) :
    LocalOn (collar A X) (representative A B) := by
  intro U V agree
  have same (x : Site n) (hx:x∈X) : transport A U x=transport A V x := by
    apply congrArg Inv.inv
    apply travel_local x (A.arm x) U V
    intro e pe qe
    exact agree e (Or.inr ⟨x,hx,pe⟩) (Or.inr ⟨x,hx,qe⟩)
  apply integral_congr_ae
  apply Eventually.of_forall
  intro k
  apply h
  intro e he tail
  unfold rotate based Lattice.gauge
  rw [same e.1 he,same _ tail,agree e (Or.inl he) (Or.inl tail)]

end YM.Integration.WilsonPhysicalAnchoredGauge

