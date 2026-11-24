import YM.Frontier6.Multi.Diff.Perturb
/-! Rough valuations along arbitrary clocks, at all finite grade, in actual
    continuum prices. Needed here before any removals from a stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I J V X Y:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}(K:Final C F S) {T : Fareway I}{a b c:ℝ} {x:I→ V→ E4}
variable (hG: Org.Grill C F)
set_option quotPrecheck false
def expenses (d:V→ℕ):ℝ:= ∑ i:V,((d i:ℝ)+2)
def wages (d:V→S.Tag):ℝ:= expenses (fun i=>(d i).1)
local notation "E"=> (Fintype.equivFin V).symm
lemma expenses_nonneg (d:V→ℕ): 0 ≤ expenses d:= Finset.sum_nonneg fun i _=> by positivity
lemma timber (v:V→ S.Tag): (totalGrade (v ∘ (Fintype.equivFin V).symm): ℝ)=wages v:=by
    unfold totalGrade MergeProof.Ribbons.Clouds wages expenses; rw [Nat.cast_sum]; simp_rw [Nat.cast_add]; exact Equiv.sum_comp E (fun i=> ((v i).1:ℝ)+2)
lemma telescope : StrictMono (Real.exp):= Real.exp_strictMono
lemma avails {j:I→ℕ}{J:Schedule} (he: Wide T x a) (hh: Bench J T j b)(ha:a<b): ∀ᶠ i in T.via, slide J (j i) (points (x i ∘ (Fintype.equivFin V).symm)):=by
    filter_upwards [he.margin hh ha] with i hi v w h using hi ((E).injective.ne h.symm)
include hG
lemma crude (hx:Wide T x a)(ha:0≤a)(v:V→ S.Tag)(s:I→ StateIndex K): T.Costs (fun i=> poll S (state K (s i)) (assembly S (x i) v)) (wages v*a):=by
    intro b hb; obtain ⟨w,hw,hW⟩:= tower_rough K (v ∘ E) hG
    have ht : Continuous (fun t:ℝ=>wages v*t):= continuous_const.mul continuous_id
    obtain ⟨c,hc,hc'⟩:= ((show ∀ᶠ c:ℝ in 𝓝[>] a,a<c from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ht.continuousAt.eventually (gt_mem_nhds hb)))).exists
    obtain ⟨j,hj⟩:= picks C.S C.path.levels.fits.mesh T c (ha.trans_lt hc)
    filter_upwards [avails hx hj hc,hx.injective,hj.infinite.eventually hW,(hj.notes hw).cheaper (T.minted b) (by rw [timber]; exact hc')] with i hi h hp ht; rw [acast,if_pos h]; exact (hp (s i) _ hi).trans ht.le
omit hG
lemma Fareway.Costs.product {Z:Type*}[SeminormedCommRing Z](U:Finset V)(f:V→ I→Z)(c:V→ℝ)(he:∀ i∈ U,T.Costs (f i) (c i)):T.Costs (fun i=>∏ x∈U,f x i) (∑ x∈U,c x):=by
   induction U using Finset.induction_on with
   | empty => simp only [sum_empty,prod_empty]; exact Fareway.Costs.const _
   | @insert i s hp ih => simp only [sum_insert hp,prod_insert hp]; exact (he i (mem_insert_self ..)).mul (ih (fun j hj=> he j (mem_insert_of_mem hj)))
section
variable (d:V→ℕ)(v:∀ i:V,I→ S.Field (d i)){p:V→ℝ} (hv:∀ i:V,T.Costs (v i) (p i)) (hx:Wide T x a) (ha:0≤a)
def medallion (h:roles S d) (i:I):ℂ:= coord d (fun j=>v j i) h
lemma attaches (p:roles S d): wages (line (S:=S) d p)=expenses d:= rfl
include hv
lemma medallion_cost (h:roles S d) : T.Costs (medallion d v h) (∑ i:V,p i):=by
   let a i:= LinearMap.toContinuousLinearMap ((board (S:=S) (d i)).coord (h i)); exact Fareway.Costs.product Finset.univ (fun i j=> a i (v i j)) p (fun i _=> (hv i).mapped (a i))
include hx ha hG
lemma votes (s:I→StateIndex K): T.Costs (fun i=> poll S (state K (s i)) (assembly S (x i) (fun j=>⟨d j,v j i⟩))) (expenses d*a+∑ i,p i):=by
    simp_rw [(deck_congr K d _ _).done K (s _),map_sum,map_smul, smul_eq_mul]
    let y(s':roles S d)(i:I):ℂ:= (medallion d v s' i)* poll S (state K (s i)) (assembly S (x i) (line d s'))
    refine Costs.sum Finset.univ y fun i _=>?_ -- order
    rw [add_comm (expenses d*a),← attaches d i]; exact (medallion_cost d v hv _).mul (crude K hG hx ha (line d i) s)
end
lemma Wide.through (x:I→ V→ E4)(c:I→ E4)(p:I→ J→ E4) (h:Aspect T x) (hh:Wide T (fun i (t:Option J)=> t.elim (c i) (p i)) 0) : Wide T (fun i=> Sum.elim (fun j=> x i j+c i) (p i)) 1:=by
    let X(v:V)(i:I):= x i v; let Y(k:J)(i:I):= p i k
    have hv(i:V)(j:J): ReachWide T (fun k=> X i k+c k) (Y j) 1:=by
       have hp:= hh (show (none:Option J)≠ some j by simp)
       -- change ReachWide T c (Y j) 0 at hp instead
       simp only [Option.elim_none,Option.elim_some] at hp; exact ReachWide.mono (T:=T) (y:=Y j) (ReachWide.motion (z:=X i) (x:=c) (y:=Y j) hp (h.1 i) zero_lt_one) zero_le_one
    rintro (i|i) (j|j) h'; dsimp only [Sum.elim_inl]; intro a ha; simpa only [add_sub_add_right_eq_sub] using h.wide (show i≠j from fun h=> h' (congr_arg _ h)) a ha
    · dsimp only [Sum.elim_inl,Sum.elim_inr]; exact hv _ _
    · dsimp only [Sum.elim_inl,Sum.elim_inr]; exact ReachWide.flip (hv _ _)
    · dsimp only [Sum.elim_inr]; have hz : some i≠some j:= fun h=>h' (congr_arg _ (Option.some_injective _ h)); have hp := hh hz; simp only [Option.elim_some] at hp; exact ReachWide.mono (T:=T) (x:=Y i) (y:=Y j) hp zero_le_one
section
variable (p:Probe S)(x:I→V→ E4) (v:V→ S.Tag) (h:Aspect T x) (c:I→ E4) (g:I→ Ortho)
def cone : I→ V ⊕ Fin p.length→ E4:=fun i=> Sum.elim (fun k:V=> x i k+c i) (fun k=> (p.roll K (g i)).exterior k+c i)
include h
lemma Wide.conic : Wide T (cone K p x c g) 1:=by
   unfold Road.cone; apply Wide.through x c (fun i (j:Fin p.length)=> (p.roll K (g i)).exterior j+c i) h; exact highlights (T:=T) (c:=c) K p g
include hG
set_option maxHeartbeats 800000 in
lemma staple : T.Costs (fun i=>(p.roll K (g i)).tip K (written K (c i) (assembly S (fun j=> x i j+c i) v))) (wages v+wages (S:=S) p.letter):=by
    let Z:= V⊕ Fin p.length; let d (i:Z):= Sum.elim (fun i=>(v i).1) (fun i=>(p.letter i).1) i;
    let f(i:Z)(j:I):S.Field (d i):= Sum.rec (motive:=fun i=>S.Field (d i)) (fun i=>(v i).2) (flying K p (g j)) i
    let w(i:I):= cone K p x c g i; have hz(j:Z): T.Costs (f j) 0:=by rcases j with i|i; exact Fareway.Costs.const _; exact Fareway.Costs.immured T (fun g:Ortho=> flying K p g i) ((continuous_apply i).comp (fly_cont K p)) g
    have he:= votes K hG d f (p:=fun _=> (0:ℝ)) hz (Wide.conic K p x h c g) zero_le_one (fun _=>none); rw [show expenses d=wages v+wages (S:=S) p.letter from ?_, mul_one,Finset.sum_const_zero, add_zero] at he; swap
    · unfold expenses wages; rw [Fintype.sum_sum_type]; rfl
    refine he.cf (Eventually.of_forall fun i=>?_); change poll S (state K none) _=poll S (state K none) (_ * assembly S (fun j=> (p.roll K (g i)).exterior j+c i) (p.roll K (g i)).letter); rw [←concatenates]; congr 1; apply congr_arg (assembly S (w i)); ext1 u; rcases u with u|u <;> rfl
end
-- at hand programs cost by finite sum or max
variable (e:ℕ)
def havens:ℝ:=∑ i:Fin (e+1), ∑ p:(hand K i.val).list,∑ b:Bool, wages (S:=S) (p.val.flip K b).letter
lemma haven_margin (i:Fin (e+1))(p:(hand K i.val).list)(b:Bool): wages (S:=S) (p.val.flip K b).letter≤ havens K e:=by
   let y(k:Fin (e+1))(z:(hand K k.val).list)(b:Bool):= wages (S:=S) (z.val.flip K b).letter; have he k z b : 0 ≤ y k z b := expenses_nonneg _; apply le_trans (Finset.single_le_sum (fun v _=>he i p v) (mem_univ b)); apply le_trans (Finset.single_le_sum (fun v _=> sum_nonneg (fun b _=> he i v b)) (mem_univ p)); exact Finset.single_le_sum (f:=fun (k:Fin (e+1))=> ∑ p:(hand K k.val).list,∑ b:Bool, y k p b) (fun k _=> sum_nonneg (fun p _=>sum_nonneg (fun b _=> he k p b))) (mem_univ i)
lemma read_expenses {c:I→ E4}{X:I→Spelling S}(hv:∀ᶠ i in T.via,Visible K (c i) e (X i)) (hy:∀ (i:Fin (e+1))(p:(hand K i.val).list)(b:Bool)(g:I→Ortho),T.Costs (fun i=> ((p.val.flip K b).roll K (g i)).tip K (written K (c i) (X i))) a): T.Costs (fun i=> album K (c i) e (X i)) a:=by
    intro b he
    let F (i):= album K (c i) e (X i); let t i:= Real.exp (T.scale i*b)
    let v (k:Fin (e+1))(p:(hand K k.val).list)(a:Bool)(i:I)(u:Ortho):= spotlight K (written K (c i) (X i)) a p.val u
    have h(k:Fin (e+1))(p:(hand K k.val).list)(a:Bool): ∀ᶠ i in T.via,∀ u, ‖v k p a i u‖ ≤ t i:= Fareway.Costs.uniform (hy k p a) he
    filter_upwards [eventually_all.mpr fun k=> eventually_all.mpr fun p=>eventually_all.mpr (h k p),hv] with i hi hp
    let w:= t i; have hw:0 ≤ w:= (Real.exp_pos _).le
    refine (pi_norm_le_iff_of_nonneg hw).2 fun j=>(pi_norm_le_iff_of_nonneg hw).2 fun p=>(pi_norm_le_iff_of_nonneg hw).2 fun b=>(ContinuousMap.norm_le _ hw).2 fun g=>?_
    rw [album,(displayed K hp).seats]; exact hi j p b g
include hG
lemma unlit (h:Aspect T x)(v:V→ S.Tag)(c:I→ E4) : T.Costs (fun i=> absorb K (c i) e (assembly S (fun j=>x i j+c i) v)) (wages v+havens K e):= (read_expenses K e (h.visible K e c v) (fun i p b g=> (staple K hG (p.val.flip K b) x v h c g).too (by linarith only [haven_margin K e i p b]))).mapped (detector K e)
end YM.Frontier6.Road
