import YM.Integration.WilsonReflectedMotionGrid
import YM.Integration.WilsonReflectedRestartedPair
/-! A separately placed signed raw original column and its
guarded finite restart use the very same transported measured coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPlacedArm
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonReflectedOriginalTwoDeposit
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)
local notation "P₀" i:max => (C₀).path.rep N p i

theorem spacing (f n:ℕ):(((C₀).S.steps f n).val:ℝ)*(C₀).S.a (f+n)=(C₀).S.a f:=by
  induction n with
  | zero=>simp [Schedule.steps]
  | succ n ih=>
    have L:((((C₀).S.block (f+n)).val:ℝ))≠0:=by exact_mod_cast ((C₀).S.block (f+n)).pos.ne'
    rw [Schedule.steps,PNat.mul_coe,Nat.cast_mul,show f+(n+1)=f+n+1 from rfl,(C₀).S.a_step]
    rw [←ih];field_simp

theorem linear {K:ℕ}(hi:K≤N)(h:f≤K)(F:space K→ℂ)(pF:Envelope F)(c:ℂ)(W:space f):
    actualTransport (C₀) (N:=N) (c • F) h W=c*actualTransport (C₀) (N:=N) F h W:=by
  let E:space K→ℂ:=fun V=>(P₀ K).eval V • F V
  have w:Integrable E (prior G _):=ActualWilsonAbsoluteTransport.weighted (C₀) R.makes hi pF
  have pay:=actualTransport_unnormalize (C₀) R.makes hi (c • F) h W
  have old:=actualTransport_unnormalize (C₀) R.makes hi F h W
  have eq:(fun V:space K=>(P₀ K).eval V • (c • F) V)=c • E:=by funext V;change (P₀ K).eval V • (c • F V)=c • ((P₀ K).eval V • F V);exact smul_comm .. 
  rw [eq,WilsonReflectedTwoGridFields.scaled R h E w c] at pay
  change _=c*gust (C₀).path N p K E f h W at pay
  rw [←old,Complex.real_smul,Complex.real_smul] at pay
  have v:((P₀ f).eval W:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (h.trans hi) W).ne'
  apply mul_left_cancel₀ v;rw [pay];ring

def original (d:ℕ)(cut:f≤N)(Y:(C₀).label d)(b:Bool)(s:Signed)(o:Site ((C₀).side f p)):Column R N p d:=
  ⟨Y,b,s,((C₀).S.toDepth cut p).embed o⟩

def atZero (d N p K:ℕ)(w:(C₀).label d)(V:Config G ((C₀).side K p)):ℂ:=
  part ((C₀).localSection d) 0 ((C₀).path.rep N p K) V w

theorem paid (d N p K:ℕ)(w:(C₀).label d):Envelope (atZero R d N p K w):=
  WilsonReflectedRestartedPair.guarded R (p:=p) (fun _=>d) N K (fun _=>0) (fun _=>w) 0

def trial {K:ℕ}(d:ℕ)(early:f≤K)(w:(C₀).label d)(b:Bool)(s:Signed)(o:Site ((C₀).side f p)):space K→ℂ:=
  (((C₀).S.a K:ℂ)^d)⁻¹ • RelayDifference.oriented (atZero R d N p K w) b s (((C₀).S.toDepth early p).embed o)

theorem facing {K:ℕ}(F:space K→ℂ)(income:Envelope F)(b:Bool)(s:Signed)(o:Site ((C₀).side K p)):Envelope (RelayDifference.oriented F b s o):=by
  obtain ⟨hf,M,hM⟩:=income
  refine ⟨?_,M,?_⟩
  · cases b
    · exact hf.comp (continuous_pull ..).measurable
    · exact continuous_star.measurable.comp (hf.comp (continuous_pull ..).measurable)
  · intro U;cases b <;> simpa [RelayDifference.oriented,RelayDifference.hand] using hM (pull s o U)

theorem trial_paid {K:ℕ}(d:ℕ)(early:f≤K)(w:(C₀).label d)(b:Bool)(s:Signed)(o:Site ((C₀).side f p)):
    Envelope (trial R (N:=N) d early w b s o):=by
  obtain ⟨hf,M,hM⟩:=facing R _ (paid R d N p K w) b s (((C₀).S.toDepth early p).embed o)
  refine ⟨hf.const_smul _,‖(((C₀).S.a K:ℂ)^d)⁻¹‖*M,fun U=>?_⟩
  rw [trial,Pi.smul_apply,norm_smul];exact mul_le_mul_of_nonneg_left (hM U) (norm_nonneg _)

end YM.Integration.WilsonReflectedPlacedArm
end
