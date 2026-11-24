import YM.RegulatorIR.Clocks.Reprice
import YM.RegulatorIR.Quadratic.Finish

/-!
# Wilson-variable reparametrization at finite regulator

Under local positive formal movement and unweighted stencil body agreement
(on inversion-quotient spin fields!). Off-cutoff continuation of polynomial
jets not costed. Never identify different gauges or prescriptions solely from
this algebra. Read θ projection in independent contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Clocks
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {p r n s d m:ℕ}{G:Gauge}{f: Side}

-- value transforms through probability and Laurent

structure Scope (s:ℕ)(B: Portrait G): Prop where
 planted : ∃ (a:ℕ) (T:Orders (Foot G)), Halo.BasisT a s B T ∧ Ranks a T

variable {H: Writing}{τ:ℝ→ℝ} (T: Binding.Scale)
def flux (T: Binding.Scale)(f:Side)(s:ℕ)(B:Portrait G)(t:ℝ):ℝ:= t⁻¹^s * goal T (vital f B) t
def lampF (T: Binding.Scale)(f:Side)(s:ℕ)(B:Portrait G):PowerSeries ℝ:= PowerSeries.mk (plotPT T (vital f B) s)
lemma aspClock {B:Portrait G}(X:Scope s B)(h:Even f.val): Script (lampF T f s B) (flux T f s B):=by
 obtain ⟨m,V,H,hv⟩:=X.planted; obtain ⟨v,hP⟩:= plain_exists T G
 let P:=(f.val:ℝ); let A:= Carto G 1 P h (show (1:ℝ)*f.val=P from one_mul _);let W:=Iris (l:=1) (P:=P) h (one_mul _) v; let V':Orders (Book G f):= fun i j=> A.scroll (V i j)
 have hz:=ark T (l:=1) (P:=P) h (one_mul _) hP; let G':=vital f B
 have he:Plan G f G':= gifted f H.origin; have hh:Canvas G T W G' V' s m:=by
    exact ⟨log_eye T h (one_mul _) hP, Halo.script H h (one_mul _),hz.format,hz.printed,fun i r he=>hv i r (fun h'=>he (by unfold V';rw [h',Deck.scroll_zero])),grade_s H h (one_mul _)⟩
 obtain ⟨Q⟩:= arrive he.tune hh h he.law
 let K:= fmat A A (finer (moon (X:=G.ColorIndex))); have hx:beneath K=costO:= sunrise ..
 have h₀: Vertex (beneath K):=by rw [hx]; exact fun x=>⟨costO_pos _,costO_null x h⟩
 let A':= axis h₀ (shines (G:=G) (l:=1) (P:=P) h (one_mul _)) h; let S':=charter G f
 have hN:Nonempty (ZeroO costO A' S'):=hx ▸ lens h₀ _ _; obtain ⟨k⟩:= hN
 have HN: storyPT T G'= fun i=>coeff i (PowerSeries.X^s*PowerSeries.mk (RangeR.expect m A' W V' S')):= (top_truth T G' h he).unique (RangeR.tongue Q k h)
 have hC := Q.LaurentEnd k h
 unfold Script; convert hC using 1
 · rfl
 ext1 i; rw [lampF,term, coeff_mk]; unfold plotPT; change storyPT T G' (s+i)= _; rw [HN];dsimp only;rw [coeff_X_pow_mul', if_pos (by omega), show s+i-s=i from by omega,coeff_mk]

variable (S: Binding.Scale)
def Relevant (P Q:Binding.Scale)(τ:ℝ→ℝ):Prop:=∀ᶠ t in Tested.germ,P.beta t/t^2=Q.beta (τ t)/(τ t)^2
-- agreement can hold for t-neighborhood; equality of projections at θ not in premise

def pitch (U V:Portrait G)(f:Side)(p q:ℕ)(τ:ℝ→ℝ):Prop:=∀ᶠ t in Tested.germ, ∀ i, t⁻¹^p * vital f U t i 1= (τ t)⁻¹^q *vital f V (τ t) i 1
variable {U V:Portrait G}(h: Scope p U)(H': Scope r V)

private lemma refineV {f:Side}{G:Gauge}{T:Scale}(A:Hook G Empty (OEdge f))(y:ℝ)(t:ℝ):
 y*rightSum (startO T) A t= (∫ i, (y* A t i 1) * Real.exp (-(T.beta t/t^2)*valueO i) ∂physical G _):=by
 unfold rightSum; simp_rw [Binding.head]; rw [← MeasureTheory.integral_const_mul]; apply integral_congr_ae;filter_upwards with i; unfold Laplace.tilt startO; rw [show -(T.beta t*valueO i)/t^2= -(T.beta t/t^2)*valueO i by ring];exact (mul_assoc ..).symm
lemma reprices (ht:Relevant T S τ)(he:pitch U V f p r τ): flux T f p U =ᶠ[Tested.germ] (flux S f r V ∘ τ):=by
 filter_upwards [he,ht] with t he ht
 change _= flux S f r V _; unfold flux goal; rw [← mul_div_assoc,← mul_div_assoc,refineV,refineV]; simp_rw [he _,ht]
 have hQ : rightSum (startO (G:=G) (f:=f) T) 1 t=rightSum (startO (G:=G) (f:=f) S) 1 (τ t):=by apply mul_left_cancel₀ (show (1:ℝ)≠0 from one_ne_zero); rw [refineV,refineV]; simp_rw [Pi.one_apply,ht]
 rw [hQ]
include h H'
lemma relabel (hg: Even f.val)(hU: Script H τ)(hq:coeff 0 H=0)(hp:Tendsto τ Tested.germ Tested.germ)(ht:Relevant T S τ)(he:pitch U V f p r τ): lampF T f p U= (lampF S f r V).subst H:= by
 have hh:=Script.bend (Outlook.tilted (aspClock S H' hg) hU hq hp) (reprices T S ht he).symm
 exact PowerSeries.ext (fun i=> congr_fun ((aspClock T h hg).unique hh) i)
end YM.RegulatorIR.Clocks
