import YM.Integration.FVA1Physical.Wilson.OrbitCumulants

/-! Uniform conversion of finite squarefree moment errors to connected errors and
arbitrary independently chosen complex test values at the same marker horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset Marker Comparison.RG02.Order Extra.Trajectories
open scoped Classical
variable {ι:Type} [DecidableEq ι] [Fintype ι] (C:Census ι) (w:ι→ℝ)

def markerScale (M:ℝ) : ℝ :=
  let t:=∑ s:C.Mode,Poly.toll w s
  (1+repeats (Fintype.card ι) (1+t*(M+2)))*(2*t)

theorem markerScale_nonneg (hw:∀i,0<w i) {M:ℝ} (hM:0≤M) : 0 ≤ markerScale C w M := by
  let t:=∑ s:C.Mode,Poly.toll w s
  have ht:0≤t:=sum_nonneg fun s _=>(Poly.worth hw s).le
  have hrep:=repeats_pos (Fintype.card ι) (1+t*(M+2)) (by positivity)
  change 0≤(1+_)*(2*t)
  positivity

/-- The complex real/imaginary error of each mode propagates through the actual
normalized marker logarithm. The coefficient depends only on the physical sup
bound and the prescribed finite marker weights. -/
theorem marker_transfer (hw:∀i,0<w i) {M ε:ℝ} (hM:0≤M) (hε:0≤ε) (small:ε≤1)
    (P Q:Poly C) (unitP:P.part C.quiet=1) (unitQ:Q.part C.quiet=1)
    (cap:∀s,‖P.part s‖≤M) (bill:∀s,‖(P-Q).part s‖≤2*ε) :
    Poly.price w (P-Q) ≤ markerScale C w M*ε ∧
    Poly.price w (connected P-connected Q) ≤ markerScale C w M*ε := by
  let t:=∑ s:C.Mode,Poly.toll w s
  have ht:0≤t:=sum_nonneg fun s _=>(Poly.worth hw s).le
  let B:=1+t*(M+2)
  have rep:=repeats_pos (Fintype.card ι) B (by dsimp [B];positivity)
  have price (F:Poly C) (K:ℝ) (h:∀s,‖F.part s‖≤K) : Poly.price w F ≤ t*K := by
    unfold Poly.price t
    rw [Finset.sum_mul]
    exact sum_le_sum fun s _=>mul_le_mul_of_nonneg_left (h s) (Poly.worth hw s).le
  have e:=price (P-Q) (2*ε) bill
  have upperP:∀s, ‖P.part s‖≤M+2:=fun s=>(cap s).trans (by linarith)
  have upperQ(s:C.Mode):‖Q.part s‖≤M+2 := by
    have hq:=norm_sub_le (P.part s) (P.part s-Q.part s)
    rw [sub_sub_cancel] at hq
    exact hq.trans ((add_le_add (cap s) (bill s)).trans (by linarith))
  have one (F:Poly C) (h:∀s,‖F.part s‖≤M+2) : Poly.price w (1-F)≤B := by
    apply (priced_sub w hw _ _).trans
    rw [Poly.one_price]
    exact add_le_add le_rfl (price F (M+2) h)
  have logs:=lip P Q w hw unitP unitQ (one P upperP) (one Q upperQ) (Fintype.card ι) (fun s=>card_le_univ s.val)
  have hn:0≤t*(2*ε):=by positivity
  change _ ≤ (1+_)*(2*t)*ε ∧ _ ≤ (1+_)*(2*t)*ε
  constructor
  · exact e.trans (by change _ ≤ (1+repeats _ B)*(2*t)*ε; nlinarith only [rep,hn,mul_nonneg rep hn])
  exact logs.trans ((mul_le_mul_of_nonneg_left e rep).trans (by change _ ≤ (1+repeats _ B)*(2*t)*ε; nlinarith only [hn]))

omit [Fintype ι] in
theorem test_marker_error (P:Poly C) (test:C.Mode→ℂ)
    (bound:∀s,‖test s‖≤Poly.toll w s) :
    ‖∑ s:C.Mode,test s*P.part s‖ ≤ Poly.price w P := by
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro s _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (bound s) (norm_nonneg _)

end YM.Integration.FVA1Physical.Round2.Curvature
