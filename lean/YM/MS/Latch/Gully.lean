import YM.MS.Latch.Place
/-!
# Feed piece with weights exp (inclusive) after removing powers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job.Belt
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff Interval
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 {J:Belt I}{A B:J.time→ℝ}{f:Moments I (E→F)}{ε:ℝ}
abbrev L (H:Belt I) := H.price.length
abbrev tstart (F:J.time):ℝ:= F.2.val
lemma within (p:J.time){t:ℝ} (H:t∈J.stream p): t∈ J.slot p.1:= H.1
variable (hf:Bound J.price (plug f) A)(hJ:Walk J)(hp:Slide J ε A B)(hx:0<ε)
include hf hJ hp hx
lemma harvest (j:ℕ):∃ C:ℝ,0<C∧∃ k:ℕ,∀ p:J.time,∀ t∈J.stream p,∀ u:E, ‖iteratedFDeriv ℝ j (f p.1 t) u‖ ≤ C* J.price.full.cheap p u^k*( B p * J.price.length p^j)* cloud p (ε/2) t:= by
   obtain ⟨C,hC,k,hk⟩:= hf.quoted j; obtain ⟨V,hV,hT⟩:= hp.moment; obtain ⟨D,hD,hU⟩:= capped hx k; refine ⟨C*V*D,by positivity,k,fun p t ht u=>?_⟩; let q:J.time:=⟨p.1,t,within p ht⟩; let v:=δf p q; have hv:0≤δf p q:= sub_nonneg.mpr (show t≤ _ from ht.2); have hb:= diffuse p q hJ rfl hv u; have hr:= hJ.length p q rfl hv; have he:=hT p q rfl hv; let S:= J.price; have hu:= S.full.cheap_pos (p:=u) (i:=p) trivial; have hz:= S.full.cheap_pos (p:=u) (i:=q) trivial; have ha:0≤ A q:= hf.nonneg q u trivial; obtain hw:= S.pos q; obtain hw':= S.pos p; have hB:= hp.target p;
   apply (hk q u trivial).trans; change C*S.full.cheap q u^k*( A q * S.length q^j ) ≤ C*V*D* S.full.cheap p u^k*( B p* S.length p^j )* exp ( -(ε/2)*δf p q )
   calc
       _ ≤ C*( S.full.cheap p u*(1+δf p q) )^k * ( V* exp ( -ε *δf p q ) *B p * S.length p^j ):= by gcongr
       _ = C*V*S.full.cheap p u ^k* ( B p * S.length p^j )*( (1+δf p q)^k * exp (-ε*δf p q) ):= by rw [mul_pow]; ring
       _ ≤ C*V*S.full.cheap p u ^k*( B p*S.length p^j )*(D *exp ( -(ε/2)*δf p q ) ):= (mul_le_mul_of_nonneg_left ( hU _ hv ) (by positivity))
       _ = _ := by ring
variable [FiniteDimensional ℝ E]
def Weather (J:Belt I)(f:Moments I (E→F)): Prop:= ∀ p:J.time, ∀ u:E,AEStronglyMeasurable (fun t=> f p.1 t u) (Mu p)
lemma atMonth (hm:Weather J f)(p:J.time) : Majorant ( Mu p ) (f p.1) := by
    have hu : ∀ᵐ t∂Mu p, ContDiff ℝ ∞ (f p.1 t) := ( ae_restrict_mem ( admit p)).mono fun t ht=> hf.smooth ⟨p.1,t,within p ht⟩;
    refine ⟨hu,fun j x=> velocity (hm p) hu j x, fun j u=>?_⟩; obtain ⟨ C,hC,k,hk⟩:= harvest hf hJ hp hx j; let R:=‖u‖+1; let S:=J.price; let Z:= S.basic p*(1+S.length p*R); let H(y:E):=S.full.cheap p y; let V:= C*Z^k*( B p*S.length p^j); have he := S.pos p;
    refine ⟨ Metric.ball 0 R,Metric.isOpen_ball.mem_nhds (by simp [R]),_,(cloudM (show 0< ε/2 by positivity) p).const_mul V,?_⟩; refine ( ae_restrict_mem ( admit p ) ).mono fun i hq x hx'=>(hk p i hq x).trans ?_; unfold V; have ha: H x>0:= Cost.cheap_pos _ trivial; have hV:=hp.target p; have ht: H x≤ Z:= by
       unfold Z H Scale.full Scale.weight; dsimp only; have hz:= S.basic_pos p; gcongr; exact (le_of_lt (by simpa using hx'))
    have hw:0≤ cloud p (ε/2) i:= ( Real.exp_pos _ ).le; change C*H x^k * (B p*S.length p^j)* _ ≤ _; gcongr
variable [CompleteSpace F]
def past (J:Belt I)(f:Moments I (E→F))(p:J.time)(x:E): F:= ∫ i, f p.1 i x ∂Mu p
lemma pastCost (hm:Weather J f): Bound J.price (past J f) B:= by
    have H:= atMonth hf hJ hp hx hm; refine ⟨ fun i=>(H i).contDiff, fun j=> ?_⟩; obtain ⟨C,hC,k,hk⟩:= harvest hf hJ hp hx j; refine ⟨ C*(ε/2)⁻¹,mul_pos hC (by positivity),k,fun p x ht=>?_⟩; dsimp only; rw [show past J f p=(fun x=>∫ t,f p.1 t x∂Mu p) from rfl,(H p).identity]; let W:=J.price.full.cheap p x; let V:= C*W^k*(B p*J.price.length p^j);
    obtain he:0<ε/2:= by positivity
    dsimp only; apply ( norm_integral_le_of_norm_le ( ( cloudM he p ).const_mul V ) ( ( ae_restrict_mem (admit p)).mono fun i hi=> hk p i hi x ))|>.trans; have hV : V≥0:= by have hu:W>0:= Cost.cheap_pos _ ht; have hh:= hp.target p; have hx:= J.price.pos p; unfold V; positivity
    rw [integral_const_mul]; apply ( mul_le_mul_of_nonneg_left (price_c he p) hV )|>.trans_eq; unfold V W; ring
end YM.MS.Latch.Job.Belt
