import YM.SchemeRG11.Plate.Reader
import YM.Pert.Align.GroundLines
import YM.Pert.Triangle.Operators
/-! First stencil, orbit ready. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Tree
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial
open scoped Classical ContDiff Topology
variable {X:Type*}[AddCommGroup X][One X] {G:Gauge}

variable (x:Four X)(i j:Axis)
abbrev Three:=Fin 3
-- explicit indices to evaluate cube
abbrev FourSteps:= Axis
def letters (A:trunk G X) : FourSteps→ G.Color:= ![First.Vleft x i A,First.Xleft x i j A,First.Vright x i j A,First.Xright x j A]
def tongue (a : FourSteps)(c:G.ColorIndex): Stem (Code G X) ℝ:= ![Finsupp.single ((x,i),c) 1,Finsupp.single ((x+step i,j),c) 1, -Finsupp.single ((x+step j,i),c) 1,-Finsupp.single ((x,j),c) 1] a
lemma spoke(a:FourSteps)(c:G.ColorIndex)(A:trunk G X): sense (cant A) (tongue x i j a c)=letters x i j A a c:=by fin_cases a <;> simp [tongue,sense, letters] <;> rfl
lemma signFace(A:trunk G X): mileage x (Lattice.square i j) A=First.curlAt x i j A:=by
 let w:=onface x [] i j A; have he:= (show mileage x (square i j) A= wideCurl A x i j from by simpa only [Bark.turn,square,Lattice.reverse, List.map_nil,List.reverse_nil,List.nil_append,List.append_nil,stop] using w); unfold First.curlAt First.linearSq First.Vleft First.Xleft First.Vright First.Xright; rw [he,wideCurl]; abel
lemma signLeap(A:trunk G X): leap x (square i j) A=First.bracketAt x i j A:=by
 let v:=First.Vleft x i A; let a:=First.Xleft x i j A; let b:=First.Vright x i j A; let c:=First.Xright x j A
 have he : x+step i+step j+(-(step i):Four X)=x+step j:=by abel
 simp only [First.bracketAt,First.bracketSq,leap] -- adjust
 simp only [square,cohort,mileage,Step.vec_pos,Step.vec_neg,he,map_zero]
 have h : x+step i+step j-step i=x+step j:=by abel
 have hb:x+step j-step j=x:=by abel
 simp [heel,Step.used,posDir,negDir,h,hb,First.Vleft, First.Xleft, First.Vright, First.Xright]; abel

def intake (a:G.ColorIndex): Stem (Code G X) ℝ:=∑ k,tongue x i j k a
lemma speak (a:G.ColorIndex)(A:trunk G X): sense (cant A) (intake x i j a)=(First.curlAt x i j A) a:=by
 simp_rw [intake,map_sum,spoke]; simp [FourSteps,Axis, Fin.sum_univ_succ,letters,First.curlAt,First.linearSq]; ring

def staple (b c:G.ColorIndex)(s t:FourSteps): Paper (Code G X) ℝ:= if s<t then leaf (tongue x i j s b)*leaf (tongue x i j t c) else 0

def stockpile(a:G.ColorIndex)(s t:FourSteps) : Paper (Code G X) ℝ:=∑ b:G.ColorIndex,∑ c:G.ColorIndex,Triangle.colorF b c a • staple x i j b c s t
lemma stockWords(a:G.ColorIndex)(s t:FourSteps)(A:trunk G X): aeval (cant A) (stockpile x i j a s t)=(if s<t then G.ad (letters x i j A s) (letters x i j A t) a else 0):=by
 unfold stockpile staple; by_cases h:s<t
 · simp only [h,↓reduceIte,_root_.map_sum,map_smul,map_mul,Haze.realTaste,spoke]
   rw [← Align.to_color]; unfold Triangle.colorF
   conv_rhs=> rw [← Triangle.sum_color (letters x i j A s), ← Triangle.sum_color (letters x i j A t)]
   simp only [map_sum, map_smul, sum_inner,real_inner_smul_left]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
   simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,sum_inner,real_inner_smul_left, Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
 simp [h]
def oreL(a:G.ColorIndex): Paper (Code G X) ℝ:=∑ s:FourSteps,∑ t:FourSteps,stockpile x i j a s t
lemma oreWords(a:G.ColorIndex)(A:trunk G X): aeval (cant A) (oreL x i j a)=(First.bracketAt x i j A) a:=by
 simp_rw [oreL,_root_.map_sum,stockWords]; simp [FourSteps, Axis, Fin.sum_univ_succ,letters,First.bracketAt, First.bracketSq]; ring

def cost: Paper (Code G X) ℝ:= if i<j then (1/2:ℝ) • ∑ a:G.ColorIndex, leaf (intake x i j a) * oreL x i j a else 0
lemma color_inner(f g:G.Color): inner ℝ f g=∑ c:G.ColorIndex, f c*g c:=by
 conv_lhs=> rw [←Triangle.sum_color g]
 simp only [inner_sum,real_inner_smul_right,Align.to_color]; apply Finset.sum_congr rfl; intro i _; ring
lemma supper(A:trunk G X): aeval (cant A) (cost x i j)=1/2 * First.costVertex x i j A:=by
 by_cases h:i<j
 · rw [cost,if_pos h,First.costVertex,if_pos h,color_inner,map_smul,_root_.map_sum]; simp only [map_mul, realTaste,speak,oreWords,smul_eq_mul]
 simp [cost,First.costVertex,h]
lemma ore_burn (a:G.ColorIndex)(A B:trunk G X): aeval (cant A) (vent (cant B) (oreL x i j a))=cohort x (square i j) A B a + cohort x (square i j) B A a:=by
 let F(A B:trunk G X) := cohort x (square i j) A B
 have hu(t:ℝ):aeval (cant A+t • cant B) (oreL x i j a)=F A A a+t*(F A B a+F B A a)+t*t*F B B a:=by rw [show cant A+t • cant B=cant (A+t•B) from rfl,oreWords,←signLeap,leap,co_add,co_add',co_add',co_s,co_s,co_s',co_s']; unfold F; simp; ring
 have hb:= tacks (cant A) (cant B) (oreL x i j a); simp_rw [hu] at hb; apply hb.unique
 let z:ℝ:=F A B a+F B A a
 convert! (((hasDerivAt_id' (0:ℝ) |>.mul_const z).const_add (F A A a)).add (((hasDerivAt_id' (0:ℝ)).mul (hasDerivAt_id' (0:ℝ))).mul_const (F B B a))) using 1; simp [F,z]

lemma wardFace (A:trunk G X)(e:Four X→G.Color) (h:i<j) : aeval (cant A) (vent (cant (ascent e)) (cost x i j)) = -(1/2:ℝ)*inner ℝ (First.curlAt x i j A) (mileage x (square i j) (spur e A)):=by
 let b:=ascent e;let Q:=cant b;let K:=mileage x (square i j) A
 have hp(a:G.ColorIndex): sense Q (intake x i j a)=0:=by change sense (cant (ascent e)) _ = _; rw [speak,← signFace,mile_stop,square_stop,sub_self]; rfl
 let U:=fun a:G.ColorIndex=>cohort x (square i j) A (ascent e) a + cohort x (square i j) (ascent e) A a
 have he(a:G.ColorIndex): U a=(G.ad K (e x+e x)-mileage x (square i j) (spur e A)) a:=by
   have ht:=test x (square i j) A e;rw [square_stop,add_comm (cohort ..)] at ht
   exact (congrArg (fun p:G.Color=>p a) (eq_sub_of_add_eq ht))
 have hh:inner ℝ K (G.ad K (e x+e x))=0:=by
   have he:G.ad K K=0:=by apply G.colorMat_injective; simp
   have ht:= G.ad_skew K K (e x+e x); rw [he,inner_zero_left] at ht; linarith only [ht]
 rw [cost,if_pos h,(vent (cant (ascent e))).map_smul]; simp only [_root_.map_sum,vent_l]; change _ = _
 simp only [taste]; dsimp only [Q,b] at hp; simp_rw [hp]; simp only [map_zero,mul_zero,add_zero,map_smul,_root_.map_sum,map_mul,Haze.realTaste,speak,ore_burn]; change (1/2:ℝ) • (∑ a,(First.curlAt x i j A a)*U a)= _; simp_rw [he]
 rw [← color_inner,inner_sub_right,← signFace,hh]; simp [smul_eq_mul]
end YM.SchemeRG11.Tree
