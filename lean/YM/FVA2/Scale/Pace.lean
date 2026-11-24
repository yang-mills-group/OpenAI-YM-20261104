import YM.FVA2.XReg.Now
import Mathlib.Topology.Algebra.Polynomial
/-!
# Bounded polynomial dependence on MS log-scale

Used at the REMOVAL step. At each fixed degree, the exponents of logarithms won't
be taken going to infinity with e.g. volume. Coefficients may. `Pace.limit`: pointwise
limit at each fixed log-scale argument. Not asserting corresponding estimates
or convergence at non-fixed (e.g. growing with the regulator) log-scale arguments.
Include the calculus on the full tower of slots, independent of occurrences. Ultimately
will also enforce the vanishing of non-homogeneous grades by testing under dilations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set Polynomial
open scoped Topology ContDiff BigOperators Classical
variable {E:Type*}{p q:ℕ}{F:Filter E}
def Price (n:ℕ)(z:ℝ→ℂ): Prop:= ∃ p:Polynomial ℂ,p.natDegree≤n ∧ z=fun x:ℝ=> p.eval (x:ℂ)
-- bounded *degree*. polynomial coefficients act on actual real log ν.
def Pace (f:E→ℝ→ℂ):= ∃ d:ℕ,∀ i:E, Price d (f i)
def Rhythm (g:ℝ→ℂ):= ∃ d, Price d g
variable {f g : ℝ→ℂ} {G H:E→ℝ→ℂ}
namespace Price
lemma of_constant (a:ℂ): Price 0 (fun _=>a):= ⟨C a,by simp, (by simp)⟩
lemma widen (h:p≤q)(hp:Price p f) : Price q f:= by obtain ⟨y,ht,hf⟩:=hp; exact ⟨y,ht.trans h,hf⟩
lemma add (h:Price p f)(he:Price q g): Price (max p q) (fun i=> f i+ g i):= by obtain ⟨y,ht,rfl⟩:=h; obtain ⟨z,hz,rfl⟩:=he; exact ⟨y+z,(natDegree_add_le _ _).trans (max_le_max ht hz),by simp⟩
lemma neg (h:Price p f): Price p (fun i=> - f i):= by obtain ⟨y,ht,rfl⟩:= h; exact ⟨-y,(natDegree_neg y).trans_le ht,by simp⟩
lemma mul (h:Price p f)(he:Price q g): Price (p+q) (fun i=> f i * g i):= by obtain ⟨y,ht,rfl⟩:=h; obtain ⟨z,hz,rfl⟩:=he; exact ⟨y*z,(natDegree_mul_le ..).trans (Nat.add_le_add ht hz),by simp⟩
lemma daylight (S:Polynomial ℝ): Price S.natDegree (fun x=> ↑(S.eval x)):= by
    refine ⟨ S.map Complex.ofRealHom, Polynomial.natDegree_map_le, funext fun i=>?_ ⟩; rw [eval_map]; exact (eval₂_at_apply Complex.ofRealHom i).symm
lemma clock (h:Price p f)(z:Polynomial ℝ): Price (p*z.natDegree) (fun i=> f (z.eval i)):= by
    obtain ⟨y,ht,rfl⟩:=h; refine ⟨y.comp (z.map Complex.ofRealHom),?_,?_⟩; · rw [natDegree_comp]; exact Nat.mul_le_mul ht natDegree_map_le
    funext i; rw [eval_comp, eval_map, show eval₂ Complex.ofRealHom (↑i) z = _ from ( show eval₂ Complex.ofRealHom ( (i:ℝ):ℂ ) z =↑( z.eval i ) from eval₂_at_apply Complex.ofRealHom i ) ] -- ambient
lemma translate (h:Price p f)(s:ℝ): Price p (fun i=> f (i-s)):= by
    obtain H:= clock h ( X-C s ); simp only [eval_sub,eval_X,eval_C] at H; refine widen ?_ H; exact (Nat.mul_le_mul (le_refl p) (by simp)).trans_eq (mul_one p)
private def bridge (n:ℕ): ( Polynomial.degreeLT ℂ (n+1) ) →ₗ[ℂ] (ℝ→ℂ) where
    toFun q x:= q.val.eval (x:ℂ)
    map_add' p q:= by funext i; exact eval_add
    map_smul' a i:= by funext x; exact eval_smul ..
private lemma covered : Price p f ↔ f∈LinearMap.range (bridge p):= by
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨⟨y, (by rw [degreeLT_succ_eq_degreeLE, mem_degreeLE,← natDegree_le_iff_degree_le]; exact hy)⟩ ,rfl⟩
    rintro ⟨⟨z,hz⟩,he⟩; rw [degreeLT_succ_eq_degreeLE,mem_degreeLE] at hz; exact ⟨z,natDegree_le_iff_degree_le.mpr hz,he.symm⟩
lemma stride [F.NeBot] (h:∀ᶠ i in F, Price p (G i))(hw:∀ i,Tendsto (fun a=>G a i) F (𝓝 (f i)) ): Price p f:=by
    let L:= bridge p; letI:= ( Polynomial.degreeLTEquiv ℂ (p+1) ).symm.finiteDimensional; haveI:= LinearMap.finiteDimensional_range L; apply covered.mpr; exact L.range.closed_of_finiteDimensional.mem_of_tendsto (tendsto_pi_nhds.mpr hw) (h.mono fun x hx=> show G x∈ (L.range:Set ( ℝ→ℂ )) from covered.mp hx)
end Price
namespace Pace
lemma narrow (t:E→ℂ): Pace (fun a (_:ℝ)=>t a):= ⟨ 0,fun i=> Price.of_constant ( t i )⟩
lemma add (h:Pace G)(he:Pace H): Pace (fun i x=> G i x+ H i x):= by obtain ⟨a,ha⟩:=h; obtain ⟨b,hb⟩:=he; exact ⟨ max a b,fun i=> ( ha i ).add ( hb i ) ⟩
lemma mul (h:Pace G)(he:Pace H): Pace (fun i x=> G i x* H i x):= by obtain ⟨a,ha⟩:=h; obtain ⟨b,hb⟩:=he; exact ⟨ a+b,fun i=> ( ha i ).mul ( hb i ) ⟩
lemma neg (h:Pace G): Pace (fun i x=> -G i x):= by obtain ⟨a,ha⟩:=h; exact ⟨a,fun i=> Price.neg (ha i) ⟩
lemma sum {W:Type*}(s: Finset W){B:W→E→ℝ→ℂ} (h:∀ i∈s,Pace (B i)): Pace (fun i x=> ∑ j∈s, B j i x):= by
    classical
    induction s using Finset.induction_on with
    | empty=>simp only [Finset.sum_empty]; exact narrow _
    | insert i s hi ih=> simp only [ Finset.sum_insert hi ]; exact add (h _ (Finset.mem_insert_self ..)) (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma prime (s:E→ℝ)(P:Polynomial ℝ) : Pace (fun i x=> (↑(P.eval (x-s i)):ℂ)):= ⟨ P.natDegree,fun _=> ( Price.daylight P ).translate _ ⟩
lemma limit [F.NeBot] (h: Pace G)(hw:∀ i,Tendsto (fun a=>G a i) F (𝓝 (f i)) ) : Rhythm f:= by obtain ⟨p,hp⟩:=h; exact ⟨p,Price.stride ( Eventually.of_forall hp ) hw⟩
end Pace
namespace Rhythm
lemma unit : Rhythm f ↔ Pace (fun _:Unit=>f):= exists_congr fun _=> ⟨ fun h _=>h, fun h=>h () ⟩
lemma from_poly : Rhythm f ↔ ∃ P:Polynomial ℂ,f=fun i:ℝ=> P.eval (i:ℂ):= by
    constructor
    · rintro ⟨p,q,h,rfl⟩; exact ⟨q,rfl⟩
    rintro ⟨p,rfl⟩; exact ⟨_,p, Nat.le_refl _,rfl⟩
lemma const (x:ℂ): Rhythm (fun _=>x):= ⟨0,Price.of_constant x⟩
lemma neg (h:Rhythm f): Rhythm (fun x=> -f x):= unit.mpr ((unit.mp h).neg)
lemma add (h: Rhythm f)(hc: Rhythm g): Rhythm (fun i=> f i+ g i):= unit.mpr ((unit.mp h).add (unit.mp hc))
lemma sub (h: Rhythm f)(hc: Rhythm g): Rhythm (fun i=> f i- g i):= by simpa [sub_eq_add_neg] using add h hc.neg
lemma mul (h: Rhythm f)(hc: Rhythm g): Rhythm (fun i=> f i* g i):= unit.mpr ((unit.mp h).mul (unit.mp hc))
lemma sum (s:Finset E)(h:∀ i∈s, Rhythm (G i)) : Rhythm (fun i=> ∑ j∈s, G j i ):= unit.mpr ( Pace.sum ( B:=fun i (_:Unit)=> G i ) s (fun a ha=>unit.mp (h a ha) ) )
lemma pre (h:Rhythm f)(P:Polynomial ℝ): Rhythm (fun i=> f ( P.eval i )):= by obtain ⟨k,hk⟩:=h; exact ⟨_,hk.clock P⟩
lemma asleep (h:Rhythm f)(he:Tendsto f atTop (𝓝 0)) : f=0:= by
    rcases from_poly.mp h with ⟨p,rfl⟩; by_cases ht:p.degree≤0
    · have hz(p':ℂ): p.eval p'=p.coeff 0:= by conv_lhs=>rw [eq_C_of_degree_le_zero ht, eval_C]
      simp_rw [hz] at he ⊢; rw [ tendsto_nhds_unique tendsto_const_nhds he ]; rfl
    have hv: Tendsto (fun i:ℝ=> ‖(i:ℂ)‖ ) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> by simpa using le_abs_self i ) tendsto_id
    exact False.elim (not_tendsto_atTop_of_tendsto_nhds (continuous_norm.continuousAt.tendsto.comp he) (tendsto_norm_atTop p (lt_of_not_ge ht) hv))
end Rhythm
end YM.FVA2.Scale
