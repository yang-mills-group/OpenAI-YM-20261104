import YM.Integration.WilsonRegisteredExteriorReturn
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact

/-! Two finite sets of genuine Wilson links can be refreshed in sequence. The
outer Haar integral keeps the true conditional mass of the first region. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredTwoPatchHaar
open Function MeasureTheory Lattice RG Wilson OriginalMarkedConditionalAction OriginalMarkedRowCovariance
open WilsonHeldExteriorLaw
open private pairing weighted from YM.Integration.WilsonHeldExteriorLaw
open private paid_mass from YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact
open scoped Classical
variable {G:Gauge}{n:Side}
local notation "X" => Config G n
local notation "η" => prior G n
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

theorem nest (S T:Support n)(x t s:X):OriginalMarkedConditionalAction.patch S (OriginalMarkedConditionalAction.patch T x t) s=OriginalMarkedConditionalAction.patch (S∪T) x (OriginalMarkedConditionalAction.patch S t s):=by
  funext e
  by_cases a:e.1∈S <;> by_cases b:e.1∈T <;> simp [OriginalMarkedConditionalAction.patch,a,b]

theorem refresh (S:Support n)(f:X→E)(ef:Envelope f):
    (∫t,∫s,f (OriginalMarkedConditionalAction.patch S t s) ∂η ∂η)=∫u,f u ∂η:=by
  have direct:=pairing (G:=G) (exterior S) (P:=fun _=>1) (f:=f) (Envelope.const 1) ef zero_lt_one (fun _=>le_rfl)
  have entry (t:X):(∫s,f (OriginalMarkedConditionalAction.patch S t s) ∂η)=projected (exterior S) (fun _=>1) f t:=by
    rw [WilsonRegisteredExteriorPatch.measured S t f ef]
    simp [projected,marginal]
  simp_rw [entry]
  simpa only [one_smul] using direct

theorem received (S T:Support n)(ext:X)(f:X→E)(ef:Envelope f):
    (∫t,∫s,f (OriginalMarkedConditionalAction.patch S (OriginalMarkedConditionalAction.patch T ext t) s) ∂η ∂η)=∫u,f (OriginalMarkedConditionalAction.patch (S∪T) ext u) ∂η:=by
  have paid:Envelope (fun u=>f (OriginalMarkedConditionalAction.patch (S∪T) ext u)):=by
    obtain ⟨b,h⟩:=ef.cost
    exact ⟨ef.meas.comp (measurable_patch _ _),b,fun u=>h _⟩
  simp_rw [nest]
  exact refresh S _ paid

def row (S:Support n)(ext:X)(p:X→ℝ)(f:X→ℂ):ℂ:=read η (fun s=>p (OriginalMarkedConditionalAction.patch S ext s)) (fun s=>f (OriginalMarkedConditionalAction.patch S ext s))
def mass (S:Support n)(ext:X)(p:X→ℝ):ℝ:=∫s,p (OriginalMarkedConditionalAction.patch S ext s) ∂η

set_option backward.isDefEq.respectTransparency false in
theorem original (S T:Support n)(ext:X)(p:X→ℝ)(f:X→ℂ)(ep:Envelope p)(positive:∀u,0<p u)(ef:Envelope f):
    row (S∪T) ext p f=read η (fun t=>mass S (OriginalMarkedConditionalAction.patch T ext t) p) (fun t=>row S (OriginalMarkedConditionalAction.patch T ext t) p f):=by
  let wF (u:X):=(p u:ℂ)*f u
  have ew:Envelope wF:=by simpa only [wF,Complex.real_smul] using weighted ep ef
  letI:IsProbabilityMeasure (prior G n):=inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Edge (Site n)=>G.probHaar)))
  have paid(x:X):0 < mass S x p:=by
    have price:Envelope (fun s=>p (OriginalMarkedConditionalAction.patch S x s)):=by
      obtain ⟨c,h⟩:=ep.cost
      exact ⟨ep.meas.comp (measurable_patch _ _),c,fun s=>h _⟩
    exact paid_mass η price (fun s=>positive _)
  have cancel (t:X):((mass S (OriginalMarkedConditionalAction.patch T ext t) p:ℝ):ℂ)*row S (OriginalMarkedConditionalAction.patch T ext t) p f=
      ∫s,wF (OriginalMarkedConditionalAction.patch S (OriginalMarkedConditionalAction.patch T ext t) s) ∂η:=by
    have nz:((mass S (OriginalMarkedConditionalAction.patch T ext t) p:ℝ):ℂ)≠0:=by exact_mod_cast (paid _).ne'
    change ((mass S _ p:ℝ):ℂ)*(((mass S _ p:ℝ):ℂ)⁻¹*(∫s,wF (OriginalMarkedConditionalAction.patch S (OriginalMarkedConditionalAction.patch T ext t) s) ∂η))=_
    rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul]
  unfold row OriginalMarkedRowCovariance.read
  change _ = ((∫t,mass S (OriginalMarkedConditionalAction.patch T ext t) p ∂η:ℝ):ℂ)⁻¹*(∫t,((mass S (OriginalMarkedConditionalAction.patch T ext t) p:ℝ):ℂ)*row S (OriginalMarkedConditionalAction.patch T ext t) p f ∂η)
  simp_rw [cancel]
  unfold mass
  rw [received S T ext p ep,received S T ext wF ew]
end YM.Integration.WilsonRegisteredTwoPatchHaar
