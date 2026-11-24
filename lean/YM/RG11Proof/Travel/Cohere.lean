import YM.RG11Proof.Fields.Winding
import YM.RG11Proof.Travel.Evolve

/-!
# Finite scale ratio intertwining of homogeneous moving frames -- algebra**

Position in common length inverse units, shrinking all separations/tensor
support uniformly. Reuse canonical Frames through horizon and the Jacobian
in `compress`. Not asserting that RG construction has those motion laws on
actual frames, let alone that iteration expanding length ratios is a legal
comparison on its domains. No rotation/contact conclusion. β,b independent
in each scheme. Scale ratio multiplies via a group action (for E_d, rank sees,
through N on a single array, no B needed). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Travel
open scoped Topology Classical BigOperators ContDiff
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Scale YM.RG11.Fields Labels Maxwell
open YM.Pert.Position (E)
variable {J P:Type*}[Fintype J]{width:P→ℕ}(w:J→ℕ){t:ℝ→Keeper width}

private theorem freedoms (L:Constraints ℝ J){K: Static J}(h:vertical (L:=L) K.b)(s:ℝ):Change.Good L (K.opposite.changeBy s):=K.opposite.law (fun k=>by
  change piece k (-K.b)∈_; rw [show piece k (-K.b)=-piece k K.b from ?_]; exact Submodule.neg_mem _ (h _)
  ext i j; simp) _

private theorem travels_grade {K:Static J}(h:graded w K.b)(s):graded w (K.opposite.changeBy s).Z:=by
   apply K.opposite.graded_aim
   intro i j he; change (-K.b) i j=_; simp [h he]

 theorem bulk_moves (q:Keeper width)(v:Mark J width):bulk w (q.move v)=bulk w v:=bulk_cast ..

private theorem stepsBoth (hh:∀ i j,(t i).chain (t j)=t (i+j))(A:ArrayAt J ℝ width)(s u:ℝ) (v:Mark J width):
   step w t s (step w t u A) v = step w t (s+u) A v:=by
  simp only [step, Keeper.move_chain, hh u s,bulk_cast]
  rw [←mul_assoc,← map_mul,←Real.exp_add, add_comm u s,←mul_add]

/-- In the homogeneous system with no unannounced shape tags, the flow API
through N. Both group and comparison parts can instead be applied to any
supplied finite-scale laws via `together` (no β). -/
 theorem stepsFlows {L:Constraints ℝ J}{N}(A:ArrayAt J ℝ width)(K:Static J)(hK:vertical (L:=L) K.b)(h:graded w K.b)(hA:Sees L A)
     (E:Keeper width)(h0:t 0=Keeper.id width)(ht:∀ i j,(t i).chain (t j)=t (i+j))
     (hp:Respiration t E A N)(he:Stem N E w A K.β K.b)(s u:ℝ):
    let q:=K.opposite.changeBy
    Change.EquivJet ((q s).compose (q u)) (q (s+u)) N:=by
   let q:=K.opposite.changeBy
   have hh(i):Change.Good L (q i):=freedoms _ hK _
   let D:=Detector.ofSees hA
   let p:=(q s).compose (q u)
   have hl:= (hh s).compose (hh u)
   have hs(v):Through N (p.act A v) ((q (s+u)).act A v):=by
     unfold p; rw [← Change.act_act (q s) (q u) (hh s).ruler.base (hh u).ruler.base]
     have hm b v:= K.against h0 E hp (fun e=> h e) he b v
     have hi : Through N ((q s).act ((q u).act A) v) ((q s).act (step w t u A) v):=Change.EquivJet.refl.act (hh s).ruler.base (fun i=>(hm u _).symm)
     rw [←acts_bulk w _ u A (q s) (hh s).ruler.base (travels_grade w (fun e=>h e) _)] at hi
     have hz:=hi.trans (demands w _ u (fun v=>(hm s v).symm) _)
     -- demands needs q s -> step s symmetry
     apply hz.trans
     rw [stepsBoth _ ht,add_comm u]
     exact hm _ _
   exact (Formal.identification D ⟨hl.ruler.base,hl.field⟩ (fun i=>(hs i).symm)).trans (Formal.identification D ⟨(hh (s+u)).ruler.base,(hh (s+u)).field⟩ (fun _=>Through.refl _)).symm

-- actual Euclid tests
 theorem stack_profile (i j:ℝ):(narrow i).chain (narrow j)=narrow (i+j):=by
    unfold narrow Keeper.chain; congr 1; funext x
    change Place.mk _ (compress _ i (compress _ j x.test))=Place.mk _ (compress _ (i+j) x.test)
    rw [compress_both]

variable {G:Gauge}{F:Frames G}{d : ℕ}
def weather {A:ShapeReport G F}{X:Adapted F d}{N:ℕ}{β:PowerSeries ℝ}{b:Square X.toBasis.J (PowerSeries ℝ)}(ha:Shows A X N β b): Static X.toBasis.J:=⟨β,b,ha.free_beta,ha.free_b⟩

 theorem scaled {A:ShapeReport G F}{B:Adapted F d}{N:ℕ}{β:PowerSeries ℝ}{b:Square B.toBasis.J (PowerSeries ℝ)}(ha:Shows A B N β b)(hG:G.Simple)(hd:6≤d)(h:A.table 1 6 3 Pert.Triangle.profileChoice (Pert.Triangle.basic F)=Pert.Triangle.cTest G):
     let q:=(weather ha).opposite.changeBy
     (∀ s v,Through N ((q s).act (A.realAt B.toBasis) v) (step (Fields.height B) narrow s (A.realAt B.toBasis) v)) ∧
     (∀ s v,Through N ((toComplex (q s)).act (A.fullAt B.toBasis) v)
          (C ((↑(Real.exp (-bulk (Fields.height B) v*s)):ℂ)) * A.fullAt B.toBasis ((narrow s).move v))) ∧
     (∀ s z,Change.EquivJet ((q s).compose (q z)) (q (s+z)) N):=by
   let K:=weather ha
   let q:=K.opposite.changeBy
   have hh: Sees B.toBasis.guard (A.realAt B.toBasis):=(A.ticket hG h hd B.toBasis (Rigidity.Ice.polar_rank F hG d)).sees
   have hp:= breath A B.toBasis ha.kernels
   have hg: graded (Fields.height B) K.b:=graded.piece_all (A:=K.b) (w:=Fields.height B) |>.mpr (fun i=>ha.adjusts i)
   have he(s)(v):Through N ((q s).act (A.realAt B.toBasis) v) (step (Fields.height B) narrow s (A.realAt B.toBasis) v):=(K.against narrow_id scalesX hp (fun e=>hg e) ha.cs s v).symm
   refine ⟨he,fun s v=> Through.symm ?_, fun s z=> stepsFlows (Fields.height B) (K:=K) (A.realAt B.toBasis) ha.valid (fun e=> hg e) hh scalesX narrow_id stack_profile hp ha.cs s z⟩
   let D(v:point B.toBasis):=C ((↑(Real.exp (-bulk (Fields.height B) v*s)):ℂ))*A.fullAt B.toBasis ((narrow s).move v)
   have ht:Anchored (q s).g:=(K.opposite.lawful_glide s).1
   refine complex_derives (A:=D) _ ht ?_ ?_ v
   · simp_rw [ShapeReport.full_real]; intro i
     refine Through.trans (q:=step (Fields.height B) narrow s (A.realAt B.toBasis) i) (fun t _=>?_) (he _ _).symm
     simp only [component,D,coeff_C_mul,step]
     have H:= congrArg (coeff t) (A.full_real B.toBasis ((narrow s).move i)); rw [component] at H
     exact (Complex.re_ofReal_mul ..).trans (congrArg (_*·) H)
   simp_rw [ShapeReport.full_imag]; intro i
   have hcomm : ShapeReport.turn B.toBasis ((narrow s).move i)=(narrow s).move (ShapeReport.turn B.toBasis i):=by
      change Sigma.mk (β:=fun p:Place=>Fin (Fields.form p)→B.toBasis.J) ⟨i.1.order, - Complex.I • compress _ s i.1.test⟩ i.2 = Sigma.mk ⟨i.1.order,compress _ s (- Complex.I • i.1.test)⟩ i.2
      rw [show compress _ s (-Complex.I • i.1.test)= -Complex.I • compress _ s i.1.test from ?_]
      apply TestFunction.ext; intro x; change jac _ _ * (-Complex.I * _)=-Complex.I * (jac _ _ * _); ring
   refine Through.trans (q:=step (Fields.height B) narrow s (A.realAt B.toBasis) (ShapeReport.turn B.toBasis i)) (fun t _=>?_) (he s _|>.symm)
   simp only [component,D,coeff_C_mul,step]
   have H:= congrArg (coeff t) (A.full_imag B.toBasis ((narrow s).move i)); rw [component,hcomm] at H
   exact (Complex.im_ofReal_mul ..).trans (congrArg (_ * ·) H)
end YM.RG11.Travel
