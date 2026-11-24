import YM.SignedWilsonExpansion.F9.EulerTop
/-! # Shelf of compact point candles

F9 comparisons at any poses through retained height. No unspecified local
operator identification, use actual stencils from the same Book. May test
along signed axes too, without requiring stationary noise covariance on the
physical witnesses. `cloth`: offsets to higher rank/crop are Coupling shifts.
-/
set_option autoImplicit false
set_option maxHeartbeats 570000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {G:Gauge}{H:Hol G}{h i j k m r d n e:ℕ}{F:Frame G h}{x: Label G h}
/-- Rather than unbounded collection of steps "locally supported" keep one compact shelf of
actual group functions. Independent translation of each occurrence only at join. -/
abbrev Use (G:Gauge)(r:ℕ):= {p:Pill G // p.rank≤r} × ℕ
abbrev Cloth (G:Gauge)(r:ℕ):= Use G r →₀ ℝ
-- give convenient statement not smashing against sum_?
def liftsC (G:Gauge)(k:ℕ): Cloth G k →ₗ[ℝ] Era G ℝ:= Finsupp.linearCombination ℝ fun y:Use G k=> trim (PowerSeries.X^y.2) y.1.val.letter
namespace Cloth
variable {S:Use G k} (v:Cloth G k)
def overC (p:Pill G)(t:p.rank≤k)(r:ℕ): Cloth G k:= Finsupp.single (⟨p,t⟩,r) 1
abbrev photo (x:Cloth G k): Era G ℝ:=liftsC G k x
lemma sees_over (p:Pill G)(t:p.rank≤k)(r:ℕ): photo (overC p t r)=trim (PowerSeries.X^r) p.letter:= by simp only [photo,liftsC,overC,Finsupp.linearCombination_single,one_smul]
lemma overD (p:Pill G)(t:p.rank≤k): photo (overC p t 0)=p.letter:=by rw [sees_over,pow_zero]; exact Prod.ext (funext fun _=> affix_plain _) (affix_plain _)
lemma recCloth {P: Cloth G k→ Prop}(x:Cloth G k)(p:P 0)(hh:∀ (T:Cloth G k)(S:Pill G)(h:S.rank≤k)(r:ℕ)(c:ℝ),P T→ P (T+c • overC S h r)): P x:=by
   refine Finsupp.induction (motive:=P) x ?_ ?_ -- syntax
   exact p
   rintro ⟨⟨S,h⟩,k⟩ x T _ _ ht
   have hz:= hh _ S h k x ht
   simpa [add_comm,overC] using hz
lemma plus_map (x y:Cloth G k): photo (x+y)=photo x+photo y:= map_add (liftsC ..) x y
lemma vert (v:ℝ)(x:Cloth G k): photo (v • x)=v • photo x:= map_smul (liftsC ..) v x
lemma receipt (x:Cloth G k): Auth k (photo x):= recCloth (P:=fun x:Cloth G k=> Auth k (photo x)) x (by rw [photo,map_zero]; exact silent ..) (fun _ s b _ _ h=>by rw [plus_map,vert,sees_over]; exact h.add ((trim_auth _ (s.solid.tall b)).μ _))
-- issue clean variant of Lens
lemma same (P Q:Pill G)(p:P.f= Q.f)(v:P.rank=Q.rank): P=Q:= by obtain ⟨f,b,t,r,z⟩:=P; obtain ⟨g,x,y,r',z'⟩:=Q; change f=g at p; change r=r' at v; subst p; subst v; rfl
lemma turn_one (P:Pill G): P.spins 1 = P:= by refine same _ _ ?_ rfl; funext U; simp [Pill.spins]
lemma turn_comp (P:Pill G)(s v:Signed): (P.spins v).spins s=P.spins (s*v):= by refine same _ _ ?_ rfl; funext U; simp [Pill.spins,pull_pull,affine]
def rotate (s:Signed)(k:ℕ): Cloth G k→ₗ[ℝ] Cloth G k:= Finsupp.linearCombination ℝ fun v:Use G k=> overC (v.1.val.spins s) v.1.property v.2
lemma rolled (s:Signed)(p:Pill G)(v:p.rank≤k)(r:ℕ):rotate (G:=G) s k (overC p v r)=overC (p.spins s) v r:=by unfold overC rotate; rw [Finsupp.linearCombination_single,one_smul]; rfl
lemma rotate_mul (s t:Signed)(x:Cloth G k): rotate s k (rotate t k x)= rotate (s*t) k x:=by
    apply recCloth x ?_ ?_; · simp only [map_zero]
    intro X S h r c hi; simp_rw [map_add,map_smul,hi,rolled]; -- need rank def transparency
    congr 2; unfold overC; congr 3; exact turn_comp ..
lemma rotates_one (x:Cloth G k) : rotate 1 k x=x :=by
    refine recCloth (P:=fun x:Cloth G k=> rotate 1 k x=x) x (map_zero _) ?_; intro _ S h r c he; rw [map_add,map_smul,he,rolled]; congr 2; unfold overC; congr 3; exact turn_one S

def raiseC (p:r≤k):Cloth G r→ₗ[ℝ] Cloth G k:= Finsupp.linearCombination ℝ fun x:Use G r=> overC x.1.val (x.1.property.trans p) x.2
lemma upRaise (p:r≤k)(v:Pill G)(h:v.rank≤r)(t:ℕ): raiseC (G:=G) p (overC v h t)=overC v (h.trans p) t:=by unfold overC raiseC; rw [Finsupp.linearCombination_single,one_smul]; rfl
lemma rises (p:r≤k)(x:Cloth G r): photo (raiseC p x)=photo x:= recCloth (P:=fun x:Cloth G r=>photo (raiseC p x)=photo x) x (by simp [photo]) (fun T x h r c he=>by rw [map_add,map_smul,upRaise,plus_map,plus_map,he,vert,vert,sees_over,sees_over])
lemma revolt (x:Cloth G k)(s:Signed): Roll s (photo x) (photo (rotate s k x)):=by
    refine recCloth (P:=fun x:Cloth G k=> Roll s (photo x) (photo (rotate s k x))) x (by rw [map_zero, photo,map_zero]; exact Roll.nil s G) ?_
    intro _ P h r t Hv
    have he : Auth k P.letter:= P.solid.tall h; have hx: Auth k (P.spins s).letter:= (P.spins s|>.solid).tall h
    rw [map_add,map_smul,rolled,plus_map,plus_map,vert,vert,sees_over,sees_over]
    exact Hv.add (receipt _) (receipt _) (((P.rolled s).aff he hx _).μ (trim_auth _ he) (trim_auth _ hx) _) ((trim_auth _ he).μ _) ((trim_auth _ hx).μ _)
lemma bangs (H:Hol G)(F:Frame G h)(x:Cloth G k)(s:Signed)(i:F.Index)(e:ℕ): row F ((photo (rotate s k x)).2 e (wr F i)) ⟨i,rfl⟩= ∑ j:F.Index, bleached F s.ortho i j*row F ((photo x).2 e (wr F j)) ⟨j,rfl⟩:=congr_fun (spectacle H F (d:=e) (revolt x s) (receipt _) (receipt _)) (i,⟨e,Nat.lt_succ_self _⟩) -- H omit
end Cloth
end YM.WilsonCoeffUV.Mer.Xa
