import YM.Integration.WilsonOriginalSignedHardWithdrawal
import YM.Comparison.RG02.Order.Pay

/-! Transport a received single-marker difference through the original older numerator and connected logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedHardHearing
open Function Finset Marker MeasureTheory Comparison.RG02.Order
open WilsonForcedMarkerLine
open scoped BigOperators Classical

variable {V:Type} {X ι:Type*} [DecidableEq V] {R:Marker.Census V} {v:V} {q:ℂ}
  {a b c f g h:Poly R}

theorem scaled (L:Line v q a b c) (k:ℂ) : Line v q (k • a) (k • b) (k • c) := by
  constructor
  · intro s absent
    rw [←smul_sub,Poly.part_smul,L.marked s absent,mul_zero]
  · rw [L.value,smul_add,←smul_sub,smul_comm k q]

theorem plus (L:Line v q a b c) (K:Line v q f g h) :
    Line v q (a+f) (b+g) (c+h) := by
  constructor
  · have be:(c+h)-(a+f)=(c-a)+(h-f):=by abel
    rw [be]
    exact pin_sum L.marked K.marked
  · rw [L.value,K.value,show (c+h)-(a+f)=(c-a)+(h-f) by abel,smul_add]
    abel

theorem finite (S:Finset ι) (A K F:ι→Poly R) (ok:∀i∈S,Line v q (A i) (K i) (F i)) :
    Line v q (∑i∈S,A i) (∑i∈S,K i) (∑i∈S,F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (same (v:=v) (q:=q) (0:Poly R))
  | insert i s fresh ih =>
    simp only [sum_insert fresh]
    exact plus (ok i (mem_insert_self _ _)) (ih (fun j hj=>ok _ (mem_insert_of_mem hj)))

theorem power (L:Line v q a b c) (n:ℕ) : Line v q (a^n) (b^n) (c^n) := by
  induction n with
  | zero => simpa using (same (v:=v) (q:=q) (1:Poly R))
  | succ n ih => simpa only [pow_succ] using product ih L

theorem connected (L:Line v q a b c) (n:ℕ) :
    Line v q (logTo n a) (logTo n b) (logTo n c) := by
  have step : Line v q (1-a) (1-b) (1-c) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using
      plus (same (v:=v) (q:=q) (1:Poly R)) (scaled L (-1))
  exact finite (range n) _ _ _ (fun i _=>scaled (power step (i+1)) (-((↑(i+1):ℂ))⁻¹))

theorem all_words [Fintype V] (A K F:ι→Poly R) (base:Summable A) (raised:Summable F)
    (line:∀i,Line v q (A i) (K i) (F i)) : Line v q (∑'i,A i) (∑'i,K i) (∑'i,F i) := by
  constructor
  · intro s absent
    rw [←raised.tsum_sub base,Poly.share (raised.sub base)]
    simpa only [tsum_zero] using (tsum_congr (fun i=>(line i).marked s absent))
  · have eq:K=fun i=>A i+q • (F i-A i):=funext (fun i=>(line i).value)
    rw [eq]
    exact (base.hasSum.add ((raised.hasSum.sub base.hasSum).const_smul q)).tsum_eq

open RG Lattice Wilson QuadraticLocal QuadraticLocal.Fusion.Attached
variable {G:Gauge} {n:Side} {P:Rep G n} {o:V→Site n} {T:Type*}
  (A K F:Hard T P.p P.activities.forced P.activities.K o R)

theorem field [Fintype V] (L:WilsonOriginalForcedMarkerMerger.Related v q A K F)
    (E:Lamps T ι G P.p o R) {w:V→ℝ} {a b:ℝ} (base:A.Paid w P.p.B P.p.supportExponent a)
    (raised:F.Paid w P.p.B P.p.supportExponent b) (hw:∀i,0<w i) (t:T) (U:Config G n):
    let G₀:Gallery T ι o P R:=⟨E,A⟩
    let G₁:Gallery T ι o P R:=⟨E,K⟩
    let G₂:Gallery T ι o P R:=⟨E,F⟩
    Line v q (G₀.density t U) (G₁.density t U) (G₂.density t U) := by
  apply scaled
  apply product (same _)
  apply all_words
  · exact Hard.packet_summing A base P.p.exponent_pos.le hw t U
  · exact Hard.packet_summing F raised P.p.exponent_pos.le hw t U
  · intro S
    by_cases allowed:P.activities.admissible P.p U S
    · simp only [packet,if_pos allowed]
      exact products S _ _ _ (fun i _=>L t i U)
    · simp only [packet,if_neg allowed]
      exact same _


variable [MeasurableSpace X] (μ:Measure X)
def mean (mass:ℂ) (A:X→Poly R) : Poly R := mass⁻¹ • Poly.inject (fun s=>∫ x,(A x).part s ∂μ)

theorem older (mass:ℂ) (A K F:X→Poly R) (origin:∀x,Line v q (A x) (K x) (F x))
    (base:∀s,Integrable (fun x=>(A x).part s) μ)
    (raised:∀s,Integrable (fun x=>(F x).part s) μ) :
    Line v q (mean μ mass A) (mean μ mass K) (mean μ mass F) := by
  apply scaled
  constructor
  · intro s no
    change (∫ x,(F x).part s ∂μ)-(∫ x,(A x).part s ∂μ)=0
    rw [←integral_sub (raised s) (base s)]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun x=>(origin x).marked s no)
  · ext1 s
    change (∫ x,(K x).part s ∂μ)=(∫ x,(A x).part s ∂μ) +
      q*((∫ x,(F x).part s ∂μ)-(∫ x,(A x).part s ∂μ))
    let d:X→ℂ:=fun x=>(F x).part s-(A x).part s
    have hd:Integrable d μ:=(raised s).sub (base s)
    calc
      (∫ x,(K x).part s ∂μ) = ∫ x,(A x).part s+q*d x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x=>congrArg (fun p:Poly R=>p.part s) (origin x).value)
      _ = _ := by
        rw [integral_add (base s) (hd.const_mul q),integral_const_mul]
        exact congrArg (fun z=>(∫ x,(A x).part s ∂μ)+q*z) (integral_sub (raised s) (base s))


theorem logged (mass:ℂ) (A K F:X→Poly R) (origin:∀x,Line v q (A x) (K x) (F x))
    (base:∀s,Integrable (fun x=>(A x).part s) μ)
    (raised:∀s,Integrable (fun x=>(F x).part s) μ) (n:ℕ) (s:R.Mode) :
    (logTo n (mean μ mass K)).part s-(logTo n (mean μ mass A)).part s =
    q*((logTo n (mean μ mass F)).part s-(logTo n (mean μ mass A)).part s) := by
  have h:=connected (older μ mass A K F origin base raised) n
  rw [h.value,Poly.part_plus,Poly.part_smul,add_sub_cancel_left]
  rfl

end YM.Integration.WilsonOriginalSignedHardHearing
