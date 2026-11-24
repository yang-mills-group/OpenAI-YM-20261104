import YM.Frontier.Tuning.Held
import YM.Frontier.Tuning.ComplexBrush
import YM.Frontier.Tuning.VertexPay
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Beet
/-! Phase cost under τ complex for a whole compulsory stock record. Subtract plume at a
SECOND positive comparison coupling but hold chart mean/displacements in physical units; this
bounds jets of differences of the nonconstant chalk+crispy multiplier (shapes alone, not exp
of that cost). Thus no estimate assuming curvature is small everywhere in a compulsory box,
and no imaginary Gaussian used as a probability. Loss in Im τ derivative scale can be
polynomial for fixed probe order j, to be removed by real→complex interpolation later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.ClockShift
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open ConnectedActivityE6 Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster Held
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q' : ConnectedActivityE6.Target G P}
variable {O : ChartRatio G}

def setBeta (R:Rep G f)(b:ℝ) : Rep G f:= {R with beta:=b}
lemma intakeBeta {x':ℝ} (T:Tube G S)(H: Intake P T x' R) (h : β ∈ Set.Icc (betaF G x' S.patch.L/2) (2 * betaF G x' S.patch.L)): Intake P T x' (setBeta R β) where
  ready:=H.ready
  received:=⟨H.received.path,H.received.clip,H.received.temp⟩
  cap:=⟨H.cap.paths,H.cap.labels⟩
  exponent:=H.exponent
  height:=H.height
  sizes:=H.sizes
  window:=h

def Centered (O : ChartRatio G) (T:Tube G S) (j:ℕ) (χ:Chi) (H K a : ℝ)(p q B:ℝ):= 
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (y:E) (U : E→ Config G c) (F : Forest S.ratio)
      (X : Coat T F) (A : Rep G f) (u:E→ Directions G f) (w : Air f G) (z : E→ Air f G), X.x=H → X.χ=χ → X.width=K → X.manifest →
       Mode U y j p → Intake P T H A → Clutch X w a A.beta q y j U u z →
        ∀ (Z:Stores S) (V:Config G f), (¬ (fun i=> X.enforce a (u i) (X.plaza (Z.dome (304*X.B))))=ᶠ[𝓝 y] fun _=>0) →
        let f i := -(chalky (vary X (U i)) (u i) V Z+ crispy (vary X (U i)) Z)
        Brush j (|B| * Z.shares) 1 (fun i=> f i - f y) y
set_option maxHeartbeats 1000000 in
lemma upload (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {O : ChartRatio G} (hO : LocalRatio O) {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop,0≤p x) (hp : Rate G L (-(1/2)) q)
    {η rT Q : ℝ} (Y : ℝ) (hr : Torch η rT Q) : ∃ B, Rate G L 1 B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D → Works P L x S T' → Tent P L x K η rT Q Y T' → ShellAccess S G x W K γ →
       Centered (P:=P) O T' j χ x K a (p x) (q x) (B x) :=by
  obtain ⟨B,hB,hG⟩:=Clutch.stilly P L D hD K γ W a χ j hO h he hp Y hr
  use fun x=>2*|B x|; refine ⟨(hB.compare (by exact Eventually.of_forall fun x=>(abs_abs _).le)).mul_left (2:ℝ),?_⟩
  filter_upwards [hG,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 2] with x h _ c f S T hS hW hΓ hT E _ _ _ y U F X R u w z hX hχ hK hM hF hR hR' Z I hf f'
  let b':=betaF G x L; let b:=if R.beta ≤  b' then 2*b' else b'/2
  have hB : Facing R (setBeta R b):=by
    refine ⟨rfl,rfl,rfl,rfl,rfl,hR.positive,?_⟩; unfold b' at b;dsimp only [setBeta,b]; split <;> linarith
  have hu := h c f S T hS hW hT E y U F X R u w z hX hχ hK (hΓ F X hX hK hM) hF hR hR' Z I hf
  have ht:= h c f S T hS hW hT E y U F X (setBeta R b) u _ _ hX hχ hK (hΓ F X hX hK hM) hF (intakeBeta T hR (β:=b) (by rw [hW.length_eq]; dsimp[b]; unfold b'; split <;> constructor <;> linarith)) (Held.clutch_scale X R _ w a hB hR') Z I hf
  let f0 i:= plumeLog (vary X (U i)) a R O (u i) I Z
  let f1 i:= plumeLog (vary X (U i)) a (setBeta R b) O (u i) I Z
  have he:= ht.separating hu
  have hh i : f1 i-f0 i=(b-R.beta)*f' i- (X.pens Z).card*(Real.log (measure_g O b)-Real.log (measure_g O R.beta)):= by
    unfold f1 f0 plumeLog; rw [show ∀ y, (vary X y).pens=X.pens from fun _=>rfl]; dsimp only [f',vary,setBeta]; ring
  have ht :1≤|b-R.beta|:=by unfold b; split <;> first | exact (le_abs_self _).trans' (by linarith) | exact (neg_le_abs _).trans' (by push Not at *; linarith)
  have v : b-R.beta≠0:=abs_pos.mp (zero_lt_one.trans_le ht)
  refine ((he.smul ((b-R.beta)⁻¹)).shimmy (q:=?_) ).climb ?_ le_rfl
  · refine Eventually.of_forall fun i=>?_ ; change f' i-f' y=(b-R.beta)⁻¹*((f1 i-f1 y)-(f0 i-f0 y)); rw [show (f1 i-f1 y)-(f0 i-f0 y)=(f1 i-f0 i)-(f1 y-f0 y) by ring,hh,hh]; field_simp; ring
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (abs_nonneg _) : (0:ℝ)≤2*|B x|)]; apply (mul_le_of_le_one_left he.nonneg ?_).trans (le_of_eq (by ring:_ + _=2*|B x| *_))
  rw [norm_inv,Real.norm_eq_abs]; exact inv_le_one_of_one_le₀ ht -- name
section charges
variable (X:Coat T F)(I:Config G f) {τ:ℂ}
private lemma centered_eq_aux (f:E→ℝ)(p:Stores S) :
    ∀ i, Complex.exp ((τ-R.beta)*f i + (X.pens p).card*(ComplexVertex.logMass O R.beta-ComplexVertex.logMass O τ)) = Complex.exp ((τ-R.beta)*f x + (X.pens p).card*(ComplexVertex.logMass O R.beta-ComplexVertex.logMass O τ))* Complex.exp ((τ-R.beta)*(f i-f x : ℝ)) := by
  intro i; rw [← Complex.exp_add];congr 1; push_cast; ring
abbrev phaseCost (τ:ℂ) (X:Coat T F) (p:Stores S):ℝ:= Real.exp (ComplexVertex.massPower X p *Real.log (‖τ‖/τ.re))
lemma penGain_norm (O:ChartRatio G) (hO:0 < O.scale) (hr:R.beta=τ.re) (ht:0<τ.re)(U:E→ Config G c)(u:E→ Directions G f)(p:Stores S):
    ‖penGain (vary X (U x)) R I (u x) O τ p‖ = phaseCost τ X p:= by
   have hh:= ComplexVertex.logPrice_re hO (z:=τ) ht
   have h' : Complex.exp ((τ-R.beta)*(-(chalky (vary X (U x)) (u x) I p+crispy (vary X (U x)) p):ℝ) + (X.pens p).card*(ComplexVertex.logMass O R.beta-ComplexVertex.logMass O τ))=penGain (vary X (U x)) R I (u x) O τ p:=rfl
   rw [← h']; rw [phaseCost, Complex.norm_exp,ComplexVertex.massPower,hr];congr 1; simp only [Complex.mul_re,Complex.sub_re,Complex.add_re,Complex.ofReal_im, Complex.ofReal_re,zero_mul,sub_self,zero_sub,mul_zero, sub_zero, Complex.natCast_im,Complex.natCast_re,hh]; ring
variable (hτ:∀ b:ℂ,Brush j (ε*‖Complex.exp b‖) 1 Complex.exp b)(hε:0≤ε)
include hτ hε
set_option quotPrecheck false
abbrev phaseSpeed (τ:ℂ)(j:ℕ)(ε d:ℝ)(p:Stores S):ℝ := ((1+j.factorial*ε)*(1+|τ.im| *(|d| * p.shares)))
lemma phaseCap (H:Centered (P:=P) O T j X.χ X.x X.width a b q d) [FiniteDimensional ℝ E]
    (hr:R.beta=τ.re) (ht:0<τ.re) (U:E→ Config G c)(u:E→ Directions G f)(m:Air f G)(z:E→Air f G)(p:Stores S) (hO:0<O.scale) (hX:X.manifest) (hU:Mode U x j b)(hR:Intake P T X.x R)(ht':Clutch X m a R.beta q x j U u z)(hi:¬ (fun i=> X.enforce a (u i) (X.plaza (p.dome (304*X.B))))=ᶠ[𝓝 x] fun _=>0):
    Brush j (phaseCost τ X p) (phaseSpeed τ j ε d p) (fun i=>penGain (vary X (U i)) R I (u i) O τ p) x:= by
  let f i:= -(chalky (vary X (U i)) (u i) I p+ crispy (vary X (U i)) p)
  have hv : (τ - R.beta) = Complex.I*Complex.ofReal τ.im:=by apply Complex.ext <;> simp [hr]
  have hs := ComplexBrush.cast_scale ((τ-R.beta):ℂ) (H E x U F X R u m z rfl rfl rfl hX hU hR ht' p I hi)
  let v i:= Complex.exp ((τ-R.beta)*(f i-f x:ℝ))
  have hh := ComplexBrush.exp_lift j hτ hs (w:=1) (by simp) hε
  simp only [hv,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,mul_one] at hh
  rw [← penGain_norm X I (x:=x) O hO hr ht U u p]
  refine ((ComplexBrush.smul_left _ hh).shimmy (Filter.Eventually.of_forall fun i=>?_) ).climb (by rw [mul_one]) le_rfl
  unfold penGain; dsimp only; rw [show (vary X (U i)).pens = X.pens from rfl,show (vary X (U x)).pens = X.pens from rfl,← Complex.exp_add,hv]; congr 1;push_cast;ring
end charges
end YM.Frontier.Tuning.ClockShift
