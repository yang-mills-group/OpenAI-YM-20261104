import YM.RegulatorIR.Pupil.Earned

/-! Tableau of protected W1 coefficients: null through order two. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil.Rules
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G : Gauge}{T:Packet (Foot G) 2}
variable (H:Rules T)(P:costM T)

def braid (T:Packet (Foot G) 2)(a b:Room)(x y:CapG G):ℝ:= ∑' z:Cover,starE T x y z * (dial a z*dial b z)
include P
lemma braided (x y:CapG G)(a b:Room) : Summable (fun z=>starE T x y z*(dial a z*dial b z)) ∧ shine T 2 (a+b) x y = shine T 2 a x y+shine T 2 b x y+ 2*braid T a b x y := by
 let f(v:Room)(z:Cover):= starE T x y z * dial v z ^2
 have hx (v): Summable (f v):= P _ _ _ 2 (by omega)
 let g(z:Cover):=starE T x y z*(dial a z*dial b z)
 have ht(z:Cover):g z=(2:ℝ)⁻¹*(f (a+b) z - f a z - f b z):=by unfold g f; rw [dial_sum];ring
 have hb: Summable g:= ((hx (a+b)|>.sub (hx a) |>.sub (hx b)).mul_left (2:ℝ)⁻¹|>.congr (fun i=>(ht i).symm))
 refine ⟨hb,?_⟩;unfold braid shine recital; change (∑' z,f (a+b) z)= (∑' z,f a z)+(∑' z,f b z)+ 2*∑' z,g z
 simp_rw [ht]; rw [tsum_mul_left, ((hx _).sub (hx a)).tsum_sub (hx b),(hx _).tsum_sub (hx a)];ring
lemma expands (x y:CapG G)(a:Room) : shine T 2 a x y= ∑ i:Axis,∑ j:Axis,a i*a j * braid T (step i) (step j) x y:=by
 let f(i j:Axis)(z:Cover):=starE T x y z *(dial (step i) z*dial (step j) z);let g(i j:Axis)(z):= a i*a j*f i j z
 have hf i j: Summable (g i j):= ((braided P x y (step i) (step j)).1).mul_left _
 have hx(z): starE T x y z*dial a z^2= ∑ i:Axis,∑ j:Axis,g i j z:=by
    unfold g f; simp_rw [dial_probe]; rw [pow_two]; unfold dial; simp_rw [Finset.sum_mul, Finset.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _;ring
 unfold shine recital; simp_rw [hx]; rw [Summable.tsum_finsetSum (fun i _=> summable_sum (fun j (_:j∈Finset.univ)=>hf i j))]; apply sum_congr rfl;intro i _; rw [Summable.tsum_finsetSum (fun j _=>hf i j)]; unfold g; simp_rw [tsum_mul_left]; rfl
omit P
lemma white (x y:CapG G)(a:Room): braid T a a x y=shine T 2 a x y:=by unfold braid shine recital; simp_rw [pow_two]
lemma roundB (x y:CapG G)(a b:Room): braid T a b x y=braid T b a x y:=tsum_congr fun i=>congr_arg (starE T _ _ i*·) (mul_comm ..)
lemma nightB(x y:CapG G)(a b:Room): braid T (-a) b x y= -braid T a b x y:=by unfold braid; simp_rw [dial_opposite,neg_mul,mul_neg]; exact tsum_neg ..
lemma mirrors (x y:Axis) : (Signed.mirror x).act (step y:Room)=if x=y then -step y else step y:=by
 rw (occs:=.pos [1]) [← Step.vec_pos,← Step.vec_rotate]
 unfold Step.vec;cases eq_or_ne x y with
 | inl h=>subst x;simp [Signed.mirror, Step.rotate,posDir]
 | inr h=>simp [Signed.mirror,h,Step.rotate,posDir]
include P H
lemma braid_dual (p:Signed)(a b:Room)(x y:CapG G): braid T (p.act a) (p.act b) (claw p x) (claw p y)= Pupil.sign p x.1*Pupil.sign p y.1*braid T a b x y :=by
 have hv := (braided P x y a b).2; have hp:= (braided P (claw p x) (claw p y) (p.act a) (p.act b)).2
 rw [← p.act_add,base_spin H P,base_spin H P,base_spin H P,hv] at hp; linarith
lemma brace_flip (k:Axis)(a b:Room)(x y:CapG G) : braid T ((Signed.mirror k).act a) ((Signed.mirror k).act b) x y=(if k=x.1 then -1 else 1)*(if k=y.1 then -1 else 1)*braid T a b x y:=by
 simpa only [Pupil.sign, Signed.mirror, decide_eq_true_eq,claw, Equiv.refl_apply,Prod.mk.eta] using braid_dual H P (Signed.mirror k) a b x y
variable {c:G.ColorIndex}(hf: token T c=0)(hG: G.Simple)
include hf hG
lemma even_shot (k: Axis)(a b:G.ColorIndex)(p:Room) : shine T 2 p (k,a) (k,b)=0:=by
 let S(x y: Room):=braid T x y (k,a) (k,b)
 have hx(i j:Axis): S (step i) (step j)=0:=by
    by_cases h:i=j
    · subst j; unfold S; rw [white];exact square_all H P hG hf .. -- order check
    have hr:= brace_flip H P i (step i) (step j) (k,a) (k,b);rw [mirrors,if_pos rfl,mirrors,if_neg h,nightB] at hr; unfold S
    simp only at hr; split at hr <;> linarith
 rw [expands P];apply sum_eq_zero;intro i _; apply sum_eq_zero;intro j _; rw [show braid T _ _ _ _= _ from hx i j,mul_zero]
omit hG hf
lemma type_odd (a b:CapG G)(h:a.1≠b.1)(i j: Axis) (hi : (i=a.1 → j≠ b.1) ∧ (i=b.1→j≠a.1)) : braid T (step i) (step j) a b=0:=by
 let p(v: Axis):Room:=step v;let S:=braid T (step i) (step j) a b
 by_cases hh:i=j
 · subst j; have hc:= brace_flip H P a.1 (step i) (step i) a b
   simp_rw [mirrors] at hc
   rw [if_pos True.intro,if_neg h] at hc; split at hc
   next H=> rw [white,white,night] at hc; rw [white]; linarith
   next H=>linarith
 have hv: (i≠a.1 ∧ j≠a.1) ∨ (i≠b.1 ∧ j≠b.1):=by grind
 obtain ⟨hv,hj⟩|⟨hv,hj⟩:=hv
 · have hc:= brace_flip H P a.1 (step i) (step j) a b; rw [mirrors,mirrors,if_neg hv.symm,if_neg hj.symm,if_pos rfl,if_neg h] at hc; linarith
 have hc:= brace_flip H P b.1 (step i) (step j) a b; rw [mirrors,mirrors,if_neg hv.symm,if_neg hj.symm,if_pos rfl,if_neg h.symm] at hc;linarith
include hf hG
lemma type_cross (a b:CapG G)(h:a.1≠b.1): braid T (step a.1) (step b.1) a b=0:=by
 let i:=a.1;let j:=b.1;let p:Room:= step i + step j
 have hc:= cloud2 H P a p b.2
 let f(k:Axis) := shine T 2 p a (k,b.2)*p k
 have hp: (∑ k:Axis,f k)=0:=hc
 have hz:shine T 2 p a b=0:=by
    rw [sum_eq_single j] at hp; have hi:p j=1:=by simp [p,h.symm,j,i]
    · unfold f at hp; rw [hi,mul_one] at hp;exact hp
    · intro k _ hk; unfold f
      by_cases hh:k=i
      · rw [hh,show shine T _ _ a (i,b.2)=0 from even_shot H P hf hG ..,zero_mul]
      have hy:p k=0:=by simp [p,hk,hh] -- p defeq
      rw [hy,mul_zero]
    exact fun h=> (h (mem_univ _)).elim
 unfold p at hz;rw [(braided P a b _ _).2, ← white,← white] at hz
 rw [type_odd H P a b h i i (by unfold i; tauto),type_odd H P a b h j j (by unfold j; grind)] at hz;linarith
lemma all_null (a b:CapG G)(x:Room): shine T 2 x a b=0:=by
 by_cases hh:a.1=b.1
 · conv_lhs=> rhs; rw [show b=(a.1,b.2) from Prod.ext hh.symm rfl]
   exact even_shot H P hf hG ..
 rw [expands P]; apply sum_eq_zero; intro i _;apply sum_eq_zero; intro j _; apply mul_eq_zero_of_right; by_cases h:i=a.1 ∧ j=b.1
 · rw [h.1,h.2];exact type_cross H P hf hG a b hh
 by_cases hv:i=b.1 ∧ j=a.1
 · rw [hv.1,hv.2,roundB];exact type_cross H P hf hG a b hh
 exact type_odd H P a b hh i j (by grind)
-- continue or cut here, exp rule handles all relative plane monomials
lemma wrinkles : MomentsP T 3 0:=by
 refine post_time _ (fun i j a n hn=> ?_) (fun i j a n hn=>?_)
 · rw [show cell i j T= _ from cell_v H (tariff i) j (area i)]; exact P _ j a n (by omega)
 rw [show cell i j T= _ from cell_v H (tariff i) j (area i)]
 interval_cases n
 · exact cloud0 H P ..
 · exact cloud1 H P ..
 exact all_null H P hf hG ..
end YM.RegulatorIR.Pupil.Rules
