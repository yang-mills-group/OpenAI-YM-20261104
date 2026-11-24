import YM.Integration.WilsonPositionScaleLawPolynomial
import YM.Integration.WilsonPositionScaleLawPanel

/-! Uniform positive-order scale changes for the original calibrated fields
from finite signed tests at a single home. All clocks, signed rows, matrix
coefficients, and the candidate at each power are prescribed before tolerances. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawQinter
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawJacobian (fieldsAt)
open WilsonPositionScaleLawIndependent (trial)
open WilsonPositionScaleLawPolynomial (pre logRatio)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

abbrev digits (d q:ℕ)(z:ℝ×Ratio):=trial Z M ν d q (logRatio z.2) (kinetic Z F J z.1)

def prediction (d q:ℕ)(z:ℝ×Ratio):=WilsonPhysicalPositionBornCandidates.operator R.family (digits Z M ν F J d q z)

def measured (d q:ℕ)(z:ℝ×Ratio): (Z.store.survey d).Bag:=
  let D:=Z.store.survey d
  D.purse (fieldsAt F J Z.store d z)-D.purse (pre Z M ν d q z.2 (kinetic Z F J z.1))

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H lead paid in
theorem original (d q:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d):∃L A:ℝ,0≤L ∧ 0≤A ∧ ∀ᶠz in sweep,
    ‖exactOp F J Z.store d z-prediction Z M ν F J d q z‖≤
      L*‖measured Z M ν F J d q z‖+A*|kinetic Z F J z.1|^(q+1):=by
  let D:=Z.store.survey d
  let T:=kinetic Z F J
  let a:=digits Z M ν F J d q
  have ht:Tendsto T trail (𝓝 0):=WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have onSweep:Tendsto (fun z:ℝ×Ratio=>T z.1) sweep (𝓝 0):=ht.comp tendsto_fst
  have ha:Tendsto a sweep (𝓝 0):=WilsonPositionScaleLawIndependent.small Z M H ν d q ht
  obtain ⟨L,hL,step⟩:=WilsonPositionScaleLawKinetic.quantitative Z M H ν F J lead paid d q raw
  obtain ⟨A,hA,move⟩:=WilsonPositionScaleLawPanel.original D
  obtain ⟨B,hB,tail⟩:=WilsonPositionScaleLawPolynomial.original Z M H ν d q
  refine ⟨L*A,L*B,mul_nonneg hL hA,mul_nonneg hL hB,?_⟩
  filter_upwards [step,Metric.tendsto_nhds.mp ha 1 zero_lt_one,Metric.tendsto_nhds.mp onSweep 1 zero_lt_one] with z fin az gz
  let x:=D.purse (fieldsAt F J Z.store d z)
  let y:=D.purse (pre Z M ν d q z.2 (T z.1))
  have htrial:‖a z‖≤1:=by simpa only [dist_zero_right] using az.le
  have hmoney:|T z.1|≤1:=by simpa only [dist_zero_right,Real.norm_eq_abs] using gz.le
  have left:=move (a z) htrial x y
  have right:‖D.itinerary (y,a z)-D.itinerary D.opening‖≤B*|T z.1|^(q+1):=tail z.2 (T z.1) hmoney
  have fee:‖D.itinerary (x,a z)-D.itinerary D.opening‖≤A*‖x-y‖+B*|T z.1|^(q+1):=by
    have three:=dist_triangle (D.itinerary (x,a z)) (D.itinerary (y,a z)) (D.itinerary D.opening)
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm] at three;exact three.trans (add_le_add left right)
  exact fin.trans ((mul_le_mul_of_nonneg_left fee hL).trans_eq (by change L*(A*‖x-y‖+B*|T z.1|^(q+1))=L*A*‖x-y‖+L*B*|T z.1|^(q+1);ring))

private theorem combine {ι E V:Type*}[Norm E][Norm V]{l:Filter ι}
    {u:ι→E}{v:ι→V}{g:ι→ℝ}{L A:ℝ}(q:ℕ)(hL:0≤L)(hA:0≤A)(small:Tendsto g l (𝓝 0))
    (bound:∀ᶠz in l,‖u z‖≤L*‖v z‖+A*|g z|^(q+1))
    (bill:v=o[l] (fun z=>g z^q)):u=o[l] (fun z=>g z^q):=by
  apply isLittleO_iff.mpr
  intro ε hε
  let δ:=ε/(L+A+1)
  have den:0<L+A+1:=by linarith
  have pos:0<δ:=div_pos hε den
  filter_upwards [bound,isLittleO_iff.mp bill pos,Metric.tendsto_nhds.mp small δ pos] with z hu hv hg
  rw [Real.norm_eq_abs,abs_pow] at hv ⊢
  have tiny:|g z|≤δ:=by simpa only [dist_zero_right,Real.norm_eq_abs] using hg.le
  have coeff:L*δ+A*|g z|≤ε:=calc
    _≤(L+A+1)*δ:=by nlinarith [mul_le_mul_of_nonneg_left tiny hA]
    _=ε:=mul_div_cancel₀ _ (ne_of_gt den)
  refine hu.trans ((add_le_add (mul_le_mul_of_nonneg_left hv hL) (le_refl _)).trans ?_)
  rw [pow_succ]
  calc
    _=(L*δ+A*|g z|)*|g z|^q:=by ring
    _≤ε*|g z|^q:=mul_le_mul_of_nonneg_right coeff (pow_nonneg (abs_nonneg _) _)

include H lead paid in
theorem qinter (d q:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d q)=o[sweep] (fun z=>kinetic Z F J z.1^q)):
    (fun z=>exactOp F J Z.store d z-prediction Z M ν F J d q z)=o[sweep] (fun z=>kinetic Z F J z.1^q):=by
  obtain ⟨L,A,hL,hA,bound⟩:=original Z M H ν F J lead paid d q raw
  exact combine (u:=fun z=>exactOp F J Z.store d z-prediction Z M ν F J d q z)
    (g:=fun z:ℝ×Ratio=>kinetic Z F J z.1) q hL hA
    ((WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).comp tendsto_fst) bound observed

end YM.Integration.WilsonPositionScaleLawQinter
end
