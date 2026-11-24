import YM.SchemeRG11.Plate.Aero
/-! Pert.Lattice exact assembly, then priced IR comparisons below. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Pile
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge} {N : Side}

def veil(o: Site N)(u:Shaft G):Pill G N:= ((wrap N u.1.1+o,u.1.2),u.2)
def adsorb(o:Site N): vellum G→ₐ[ℝ] Paper (Pill G N) ℝ:=rename (veil o)
lemma readAd(o:Site N)(q:vellum G)(A:trunk G (Per N)): aeval (cant A) (adsorb o q)= aeval (cant (absorb o A)) q:=by unfold adsorb; rw [aeval_rename]; rfl
lemma announce(p:Paper (Pill G N) ℝ):(∫ x:Orb.Coords G N,Complex.ofReal (aeval (cant (Orb.expand G N x).val) p) ∂Orb.data G N)= Complex.ofReal ((spray G N).avg p):=by
 let D:= SO G N
 have hx := introP (MvPolynomial.map Complex.ofRealHom p); unfold SO at hx; rw [Dose.mapped_avg] at hx; refine Eq.trans ?_ hx; congr 1; funext x
 simp_rw [record]
 clear hx
 induction p using MvPolynomial.induction_on with
 | C c=> simp only [map_C,aeval_C];rfl
 | add a b ha hb=> rw [map_add,map_add,map_add,Complex.ofReal_add, ha,hb]
 | mul_X a i h=> rw [map_mul (MvPolynomial.map _),map_X,map_mul,map_mul,aeval_X,aeval_X, Complex.ofReal_mul,h]

-- polynomial equality helper
lemma viewers {X : Type*}{p q:Paper (Code G X) ℝ} (he:∀ A:trunk G X, aeval (cant A) p=aeval (cant A) q) :p=q:=by apply MvPolynomial.funext; intro z; rw [← cant_inv z]; exact he _
lemma induced(o:Site N)(x:Cover)(i j:Axis): adsorb (G:=G) o (cost x i j)=cost (wrap N x+o) i j:=by
 apply viewers; intro A; rw [readAd, supper,supper]
 unfold First.costVertex; split
 · unfold First.curlAt First.bracketAt First.Vleft First.Xleft First.Vright First.Xright Bark.absorb
   simp only [map_add, wrap_step]; rw [add_right_comm (wrap N x) o,add_right_comm (wrap N x) o]
 rfl
variable {I:Type}[DecidableEq I] (s:Finset I)(t:I→Site N)
def faces(G:Gauge)(N:Side):Paper (Pill G N) ℝ:= -(1/2:ℝ) • ∑ x : Site N,∑ i:Axis,∑ j:Axis, cost x i j
def lined(h:ℝ)(p:I→pLabel G): Paper (Pill G N) ℝ:=∏ i∈s, adsorb (t i) (castZero h (p i))
def dust(h:ℝ)(p:I→pLabel G): Paper (Pill G N) ℝ:=
 faces G N * lined s t h p + ∑ i∈s,adsorb (t i) (castFirst h (p i))*lined (s.erase i) t h p
lemma faceTotal(c:Orb.Coords G N): First.cubic c=Complex.ofReal (aeval (cant (Orb.expand G N c).val) (faces G N)):=by rw [First.total_vertex]; apply congrArg; simp_rw [faces,map_smul,_root_.map_sum,supper,smul_eq_mul, ← Finset.mul_sum]; unfold First.vertexW; ring
abbrev realCast (p:pLabel G):Pol G := MvPolynomial.map Complex.ofRealHom p
omit [DecidableEq I] in
lemma tape(h:ℝ)(p:I→pLabel G)(d:ℕ)(hp:∀ i,Full.within (realCast (p i)) d)(x:Orb.Coords G N): First.line s t h (fun _=>d) (fun i=>realCast (p i)) x=Complex.ofReal (aeval (cant (Orb.expand G N x).val) (lined s t h p)):=by
 simp only [First.line, First.tube, First.lead,lined,map_prod,Complex.ofReal_prod]
 refine Finset.prod_congr rfl fun i _=>?_ ; rw [readAd]; exact (Pile.script h _ x d (p i) (hp i)).1
lemma allowing(h:ℝ)(p:I→pLabel G)(d:ℕ)(hp:∀ i,Full.within (realCast (p i)) d): PowerSeries.constantCoeff (Full.amplitude (fun _=>d) h s t (fun i=>realCast (p i)))= Complex.ofReal ((spray G N).avg (lined s t h p)):=by
 unfold amplitude; rw [Warp.normalize_zero,← announce]; refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
 dsimp only; rw [First.product_exact, map_prod]; exact tape s t h p d hp x
lemma charging(h:ℝ)(p:I→pLabel G)(d:ℕ)(hp:∀ i,Full.within (realCast (p i)) d)(hg:G.Simple): PowerSeries.coeff 1 (Full.amplitude (fun _=>d) h s t (fun i=>realCast (p i)))=Complex.ofReal ((spray G N).avg (dust s t h p)):=by
 let f i:= realCast (p i); let cap : I→ℕ:=fun _=>d
 change First.first _=_
 rw [First.first_amplitude s _ _ cap _ hg]
 unfold First.exposed dust; rw [map_add,map_sum, Complex.ofReal_add, Complex.ofReal_sum]; congr 1
 · rw [← announce]; simp only [map_mul,Complex.ofReal_mul]; refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_); dsimp only [cap]; rw [faceTotal,tape s t h p d hp x]
 refine Finset.sum_congr rfl fun i hi=>?_
 rw [← announce]; simp only [map_mul,Complex.ofReal_mul]; refine integral_congr_ae (Filter.Eventually.of_forall fun x=>?_)
 dsimp only [cap]; rw [First.varied,tape _ _ h p d hp,readAd]; congr 1; exact (Pile.script h _ x d (p i) (hp i)).2
end YM.SchemeRG11.Pile
