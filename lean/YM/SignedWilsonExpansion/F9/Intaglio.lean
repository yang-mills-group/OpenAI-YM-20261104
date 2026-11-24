import YM.SignedWilsonExpansion.F9.Launch
import YM.FVA2.BareOrb
import YM.FormalOPE.RG10.Ward.LatticeTurn
/-!
# Same top stencil as the finite even epoch

At arbitrary position & wrap (additional apertures in the next lemmas for
actual *compensation* Ward replacement). `Body.side` not an incidental choice.
Rank-budgeted Laurent terms only evaluated after one faithful stencil, shared
by all lookups at cut. Kinetic clocks remain OWN; linear arith. Institution
comparison to file uses actual K cutoff history & turns as separately imposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
-- namespaces conflict check
variable {G:Gauge}{H:Hol G}{h i j k m r d n l:ℕ}{F:Frame G h}{x: Label G h}{P:Period}
namespace StationA
open XSpace
variable {s:Signed}
lemma proxy {s : Side} (o:Site s) {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {f:CoverConfig G→ E}(p:Maskable f): Proxy (WardBin.places o f):=by
    obtain ⟨S,F,h,he⟩:= p; let W:ArrayOf G s → scopeShadow G S:= fun y i=> y (edgeAt i.val o); refine ⟨F∘W,h.of_le le_top|>.comp (contDiff_pi.mpr fun i=> contDiff_apply ..),funext fun U=> he _⟩
-- auxiliary variant holds even under products. proxy ∞ sufficient for IBP, Taylor formal expand actually needs each order through crop=real data.
lemma respect (p:Pill G) {s:Side}(o:Site s): respects (places o p.f):= fun _ _ U=>by simp only [places,Function.comp_apply,expandAt_gauge]; exact p.inv _ _
lemma candle (p:Pill G){s:Side}(o:Site s): PreTest (places o p.f):= (proxy _ p.valid).active (respect p o)
section stage
variable (T:P.Tree)
lemma flies {F:CoverConfig G→ℝ}(f:Maskable F)(o: P.Sites): ContDiff ℝ ω (WardBin.places o F ∘ T.links):=by
    obtain ⟨S,F',h,he⟩:= f; rw [funext he]; refine h.comp (f:=fun u=> body (expandAt o (T.links u)) S) ?_
    apply contDiff_pi.mpr; intro i; unfold body expandAt; simp_rw [T.links_apply]; exact G.exp_jet.comp (((contDiff_apply ..)).comp (T.covering (E:=G.Color)|>.toContinuousLinearMap.contDiff))
lemma attendance {f: Config G P.side→ℝ}: ContDiff ℝ ω (f ∘ T.links) → ContDiffAt ℝ ω (Complex.ofRealCLM ∘ (f ∘ T.links)) 0:= fun h=> Complex.ofRealCLM.contDiff.contDiffAt.comp _ h.contDiffAt
lemma expands (V:T.Field G)(o:P.Sites)(t:ℝ) : expandAt o (T.links (t • V))=roof (T.covering V ∘ (fun i=>edgeAt i o)) t:=by
    funext i; unfold expandAt roof; rw [T.links_apply, map_smul]; rfl
lemma raw_money (f:Pill G) (l:ℕ)(o:P.Sites) (ht:l<f.rank): PowerSeries.coeff l (BareOrb.stencil T (places o f.f))=0:=by
    let F:T.Field G→ ℝ:=places o f.f ∘ T.links; have hF: ContDiff ℝ ω F:= flies T f.valid o
    apply XSpace.Taylor.from_real (T.basis G); intro x; unfold BareOrb.stencil TreeFormal.enter; rw [XSpace.Taylor.expand_coeff,XSpace.Taylor.divided_realEval, map_zero]; swap; · exact hF.contDiffAt.of_le le_top
    let P(t:ℝ):=t • x; have he: ContDiff ℝ ω P:=(ContinuousLinearMap.id ℝ ℝ|>.smulRight x).contDiff
    change Complex.ofReal (Tensor.diagonal (Tensor.coeff F l 0) x)=0; rw [← leading_tensor x F (hF.contDiffAt.of_le le_top)]; apply (Complex.ofReal_eq_zero ..).mpr -- check
    obtain ⟨C,hc,H⟩:= f.bound (T.covering x ∘ (fun i=>edgeAt i o)); apply ray_leading _ (((hF.comp he).contDiffAt).of_le le_top) ht C (H.mono fun t ht=>?_); change ‖f.f (expandAt o (T.links (t • x)))‖≤_; rw [expands T]; exact ht

def propose (o:P.Sites)(v:Pill G): Bare.Series T G:= PowerSeries.mk fun i=> PowerSeries.coeff (i+v.rank) (BareOrb.stencil T (places o v.f))
lemma apex (o:P.Sites)(v:Pill G): X^v.rank* propose T o v=BareOrb.stencil T (places o v.f):=by
    apply PowerSeries.ext; intro i; rw [coeff_X_pow_mul']; split; next h=> rw [propose,PowerSeries.coeff_mk,Nat.sub_add_cancel h]
    exact (raw_money T _ _ _ (by omega)).symm

def requesting (o:P.Sites)(k:ℕ): Cloth G k→ₗ[ℝ] Bare.Series T G:= Finsupp.linearCombination ℝ fun y: Xa.Use G k=> (PowerSeries.X^y.2) * propose T o y.1.val
lemma request_card (o:P.Sites)(v:Pill G)(h:v.rank≤k)(l:ℕ): requesting T o k (Cloth.overC v h l)=X^l*propose T o v:=by simp only [Cloth.overC, requesting, Finsupp.linearCombination_single,one_smul]
lemma request_crest (o:P.Sites)(v:Pill G)(h:v.rank≤k): requesting T o k (Cloth.overC v h 0)=propose T o v:= by rw [request_card,pow_zero,one_mul]
lemma paid_ascent (x:Cloth G k)(p:k≤ m)(o:P.Sites): requesting T o _ (raiseC p x)= requesting T o _ x:=by
    apply Cloth.recCloth x ?_ ?_; · simp only [map_zero]
    intro V X he r c h; simp_rw [map_add,map_smul,upRaise,h,request_card]
lemma allow (v:Label G h)(u:v∈Grade (d,k))(p:Labels.realBar v=v)(o:P.Sites)(A: XSpace.Survey G H h):
    propose T o (Pill.curlP A v u)= XSpace.Bare.raw T A o v.val:=by
   apply mul_left_cancel₀ (a:=PowerSeries.X^k) (pow_ne_zero _ X_ne_zero); rw [XSpace.Bare.coefficient_weight T A o k ?_, show PowerSeries.X^k * _= _ from apex T o (Pill.curlP A v u)] -- maybe arguments; tactic
   swap; · intro i hi; have he:=(pure_grade _ _|>.1 u) (MvPolynomial.mem_support_iff.mp hi); rw [weight_slot] at he; exact congr_arg Prod.snd he.symm
   apply congr_arg (XSpace.Taylor.expandTaylor (T.basis G)); funext x; exact (Pill.real_eval v p (expand _ (A.reading (expandAt o (T.links x))))).symm
lemma pinwheel (v:Label G h)(u:v∈Grade (h,k))(p:realBar v=v)(o:P.Sites)(A:XSpace.Survey G H h)(q:k≤ h): requesting T o _ (permitT A u)= XSpace.Bare.column T A o v:=by
    let S:= A.insertW (-1) v; let f(y:Label G h):= XSpace.Bare.raw T A o y.val; let P(i:Fin (h+1))(j:Fin k):= gradePart (i.val,j.val) (S-v); let c:= ∑ i:Fin (h+1),∑ j:Fin k,P i j
    rw [permitT,map_add,map_sum, request_crest,allow T v u p,Bare.column_formula,A.insertW_val]
    have hx:Next.Rank.Normal.milk (A.selfCov (-1)) v.val=v.val+c.val:=by
       have ht:S=v+c:=by rw [← show S-v=c from rebate A u q]; abel
       exact congr_arg Subtype.val ht
    rw [hx]
    unfold c XSpace.Bare.raw; rw [map_add, AddSubmonoidClass.coe_finsetSum,map_sum,add_right_inj]; apply Finset.sum_congr rfl; intro i _; rw [map_sum,AddSubmonoidClass.coe_finsetSum,map_sum]; exact Finset.sum_congr rfl fun j _=> by rw [request_crest]; exact allow T _ _ (color_pigment A p i j) _ _
end stage
end StationA
end YM.WilsonCoeffUV.Mer.Xa
