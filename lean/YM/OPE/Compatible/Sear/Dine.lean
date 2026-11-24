import YM.OPE.Compatible.Ocher.Vin
import YM.OPE.Rate
/-! # Budgeted F-measurable sequences stochastic/emissions. Useful Wick read currency independent of horizon -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type*}{s t c:ℝ}{i j k:ℕ}{T:I→ℝ}{l:Filter I}
open PertExtension Series Libra GaussianScore Jargon
abbrev PayR (X:I→Type*) := (i:I)→ X i → ℝ
variable {X:I→ Type*}{Yz:I→Type*}[∀ i,MeasurableSpace (X i)]{μ:∀ i,Measure (X i)}
def Grain (μ:∀ i,Measure (X i))(l:Filter I)(T:I→ℝ)(a:PayR X)(s:ℝ):Prop:= ∀ j:ℕ,0 < j → ∃ A:I→ℝ, RateLE l T A s∧ ∀ᶠ i in l, Fault (μ i) j (a i) (A i)
variable {p q:PayR X}
namespace Grain
lemma mint (h:Grain μ l T p s)(hv:s ≤ t): Grain μ l T p t:=by intro i hi; obtain ⟨A,ha,H⟩:=h i hi; exact ⟨A,ha.mono hv,H⟩
lemma shift (h:Grain μ l T p s) (h':∀ᶠ i in l,p i=q i) : Grain μ l T q s:=by -- EventuallyEq dependent? f type.
    intro i hi; obtain ⟨A,ha,H⟩:=h i hi;exact ⟨A,ha,(h'.and H).mono fun j hh=>hh.1 ▸ hh.2⟩
lemma mul (h:Grain μ l T p s)(ht:Grain μ l T q t): Grain μ l T (fun i x=> p i x*q i x) (s+t):=by
       intro i hi; obtain ⟨a,ha,H⟩:= h (2*i) (by omega); obtain ⟨b,hb,H'⟩:= ht (2*i) (by omega); exact ⟨_,ha.mul hb,(H.and H').mono fun i he=>he.1.double he.2 hi⟩
lemma add (h:Grain μ l T p s)(ht:Grain μ l T q s)(hL:Tendsto T l atTop): Grain μ l T (fun i x=>p i x+q i x) s:=by
       intro i hi; obtain ⟨a,ha,H⟩:= h i hi; obtain ⟨b,hb,H'⟩:=ht i hi; exact ⟨_,ha.add hb hL,(H.and H').mono fun i he=> he.1.add he.2 hi⟩
lemma sub (h:Grain μ l T p s)(ht:Grain μ l T q s)(hL:Tendsto T l atTop): Grain μ l T (fun i x=>p i x-q i x) s:=by
       intro i hi; obtain ⟨a,ha,H⟩:= h i hi; obtain ⟨b,hb,H'⟩:=ht i hi; exact ⟨_,ha.add hb hL,(H.and H').mono fun i he=> he.1.sub he.2 hi⟩
lemma norm (h:Grain μ l T p s): Grain μ l T (fun i x=>‖p i x‖) s:= by intro i hi; obtain ⟨a,ha,H⟩:= h i hi; exact ⟨a,ha,H.mono fun _ hi=> hi.NormT⟩
lemma of_le (h:Grain μ l T p s) (hf:∀ᶠ i in l, AEStronglyMeasurable (q i) (μ i)) (he:∀ᶠ i in l, ∀ᵐ x ∂μ i, ‖q i x‖ ≤ ‖p i x‖): Grain μ l T q s:=by
       intro i hi; obtain ⟨a,ha,H⟩:= h i hi; exact ⟨a,ha,(H.and (hf.and he)).mono fun j hi=>hi.1.ofLe hi.2.1 hi.2.2⟩
variable [∀ i, IsProbabilityMeasure (μ i)]
lemma const {p:I→ℝ}(h:RateLE l T p s): Grain μ l T (fun i _=>p i) s:= fun _ _=>⟨_,h.norm,Eventually.of_forall fun _=>Fault.constant _⟩
lemma pow (h:Grain μ l T p 0)(hL:Tendsto T l atTop)(k:ℕ):Grain μ l T (fun i x=>p i x^k) 0:=by induction k with
   | zero=>apply (const (μ:=μ) (RateLE.const 1 hL)).shift; filter_upwards with i; simp
   | succ k hk=>simpa only[pow_succ,zero_add] using! hk.mul h
lemma integral (h:Grain μ l T p s): (∀ᶠ i in l,Integrable (p i) (μ i)) ∧ RateLE l T (fun i=>∫ x,p i x ∂μ i) s:=by
      obtain ⟨a,ha,H⟩:=h 1 (by decide); exact ⟨H.mono (fun _ h=> h.rich.integrable (by norm_num)),RateLE.transfer ha (H.mono fun i h=>(h.pays le_rfl).trans (Real.le_norm_self _))⟩
end Grain
end YM.OPE.Cinders
