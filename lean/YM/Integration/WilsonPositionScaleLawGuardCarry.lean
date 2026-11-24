import YM.Integration.WilsonPositionScaleLawGuardFieldSize

/-! A finite pretarget shift in coupling order pays the actual homogeneous two-radius error evaluated on every fixed original field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardCarry
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize Asymptotics
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable {ι X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]{l:Filter ι}

theorem allocation {ε C:ℝ}(ep:0<ε)(hc:0≤C):ε/(C+1)*C≤ε:=by
  have h:0<C+1:=by linarith
  calc _≤(ε/(C+1))*(C+1):=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (div_pos ep h).le
       _=ε:=div_mul_cancel₀ ε h.ne'

theorem applied (A:ι→X→L[ℂ]X)(v:ι→X)(g:ι→ℝ)(p q:ℕ){C:ℝ}(hc:0≤C)
    (price:∀ᶠi in l,‖v i‖*|g i|^(2*p)≤C)(paid:A=o[l] (fun i=>g i^(q+2*p))):
    (fun i=>(A i) (v i))=o[l] (fun i=>g i^q):=by
  apply isLittleO_iff.mpr;intro ε hp
  let a:=ε/(C+1)
  have ha:0<a:=div_pos hp (by linarith)
  filter_upwards [price,isLittleO_iff.mp paid ha] with i input fee
  have measured:‖A i‖≤a*|g i|^(q+2*p):=by simpa only [Real.norm_eq_abs,abs_pow] using fee
  calc
    _≤‖A i‖*‖v i‖:=(A i).le_opNorm _
    _≤(a*|g i|^(q+2*p))*‖v i‖:=mul_le_mul_of_nonneg_right measured (norm_nonneg _)
    _=(a*|g i|^q)*(‖v i‖*|g i|^(2*p)):=by rw [pow_add];ring
    _≤(a*|g i|^q)*C:=mul_le_mul_of_nonneg_left input (mul_nonneg ha.le (pow_nonneg (abs_nonneg _) _))
    _=(a*C)*|g i|^q:=by ring
    _≤_:=by rw [Real.norm_eq_abs,abs_pow];exact mul_le_mul_of_nonneg_right (allocation hp hc) (pow_nonneg (abs_nonneg _) _)

theorem mapped (A:X→L[ℂ]X)(v:ι→X)(g:ι→ℝ)(paid:v=o[l] g):(fun i=>A (v i))=o[l] g:=by
  apply isLittleO_iff.mpr;intro ε hp
  let a:=ε/(‖A‖+1)
  have ha:0<a:=div_pos hp (by positivity)
  filter_upwards [isLittleO_iff.mp paid ha] with i fee
  calc _≤‖A‖*‖v i‖:=A.le_opNorm _
       _≤‖A‖*(a*‖g i‖):=mul_le_mul_of_nonneg_left fee (norm_nonneg _)
       _=(a*‖A‖)*‖g i‖:=by ring
       _≤_:=mul_le_mul_of_nonneg_right (allocation hp (norm_nonneg A)) (norm_nonneg _)

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
def term (d Q:ℕ)(O:S.Field d)(w:ℝ×Ratio):= (dressed Z F J d w.1 w.2-expected F J Z M ν d Q w.1 w.2) (physical F J Z d (w.2.val*w.1) O)

include H in
theorem original (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2):
    ∃p:ℕ,∀q:ℕ,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d (q+2*p)→∀O:S.Field d,
      term Z M ν F J d (q+2*p) O=o[sweep] (fun w=>gθ w.1^q):=by
  obtain ⟨p,entries⟩:=WilsonPositionScaleLawGuardFieldSize.original Z M H ν F J d funded law
  refine ⟨p,?_⟩;intro q measured O
  obtain ⟨C,hC,read⟩:=entries O
  apply applied (p:=p) (q:=q) _ _ _ hC _ measured
  exact (tendsto_fst.eventually read).mono fun w bill=>bill w.2

end YM.Integration.WilsonPositionScaleLawGuardCarry
