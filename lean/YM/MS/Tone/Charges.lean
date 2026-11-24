import YM.MS.Tone.Haar
/-!
# One-body ∆ lines

All local jets at bare. Cover loop absolutely (compact moment). BV canonical signs in symbols include half. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Landau Momentum Flux
open MeasureTheory
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}
local notation "Z"=> Branch G Axis
local notation "P"=> Spectrum G
local notation "V"=> LightMode G QP
abbrev Kzone (G:Gauge): Flux (Branch G Axis) QP ℂ:= Landau.choir (laplace (fun _=>1)) Momentum.wave
lemma stipend (F:Z→Z→ℂ)(x:QP)(w:Momentum Axis→ℝ)(T:QP→Momentum Axis): ∑ i:Z,∑ j:Z,Landau.choir (laplace w) T i j x*F i j = ∑ i:ToneS G,((P).fee i:ℂ)*((w (T x):ℂ)/2)*(F ((P).dual i) ((P).plain i)+ F ((P).plain i) ((P).dual i)) := by
    unfold Landau.choir; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool,Fintype.sum_sum_type]; -- actually huge sums
    simp [laplace,delta,leggin, signA, Spectrum,Bonded.fee,p,parity,ite_mul,ite_div,Fintype.sum_prod_type,apply_ite,cross]
    simp only [mul_add, neg_div,neg_mul,Finset.sum_add_distrib, Finset.sum_neg_distrib]; abel
lemma zeroX (k l:Z)(p:QP): Kzone G k l p= Kzone G k l 0:=by
    unfold Kzone Landau.choir; split; swap; rfl
    rcases k with ⟨⟨_|k,_|_⟩,s⟩ <;> rcases l with ⟨⟨_|l,_|_⟩,u⟩ <;> rfl
lemma offFee (a:ToneS G) (x:Cover): bornv ((P).dual a,x)=bornv ((P).plain a,x):= by rcases a with ⟨_,_⟩|_ <;> rfl
lemma integr (f:QP→ℂ)(h:Continuous f): Integrable f μzone:= by letI : ProperSpace QP:= FiniteDimensional.proper ℝ QP; exact h.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
lemma atZeroFit (p:QP)(F:Dot G Cover)(l:List V): trc (Kzone G) p (run F) l=∑ i:ToneS G,(((P).fee i:ℂ)*(1/2))* (run F (((P).dual i,p)::((P).plain i,-p)::l)+run F (((P).plain i,p)::((P).dual i,-p)::l)):= by
   rw [at_trc]; convert! stipend (fun i j=> run F ((i,p)::(j,-p)::l)) p (fun _=>1) wave using 1
lemma twice (a b:Z)(l:List V)(F:Dot G Cover){s:Finset Cover}(h:BoundBy (s:Set Cover) F)(p q:QP) : run F ((a,p)::(b,q)::l)=∑ i∈s,∑ j∈s,bill p (bornv (a,i))*bill q (bornv (b,j))*run (enter (b,j) (enter (a,i) F)) l:= by
    rw [grows _ h]; apply Finset.sum_congr rfl; intro i _; rw [grows _ (s:=s) (show BoundBy (s:Set Cover) (enter (a,i) F) from Uses.drop _ h),Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
lemma twice_cont (a b:Z)(l:List V)(F:Dot G Cover): Continuous (fun p=>run F ((a,p)::(b,-p)::l)):= by
    obtain ⟨s,hs⟩:=obliges F; simp_rw [twice a b l F hs]; unfold bill pairing; fun_prop
lemma twice_int (a b:Z)(l:List V)(F:Dot G Cover)(H:offset a.1=offset b.1):
    (∫ p,run F ((a,p)::(b,-p)::l) ∂μzone)=run (heart a b F) l:= by
    obtain ⟨s,hs⟩:=obliges F; simp_rw [twice _ _ _ _ hs]; rw [heart_by a b F hs,map_sum,Finset.sum_apply, integral_finsetSum]; swap
    · intro i _; apply integr; unfold bill pairing; fun_prop
    apply Finset.sum_congr rfl; intro i hi; rw [integral_finsetSum]; swap
    · intro k _; apply integr; unfold bill pairing; fun_prop
    simp only [integral_mul_const]; simp_rw [bornv,choir_pair H,ite_mul,one_mul,zero_mul]; rw [Finset.sum_eq_single i]; simp; · intro _ _ hx; rw [if_neg (Ne.symm hx)]
    exact fun h=> (h hi).elim
lemma heart_sym {h q:Z} (F:Dot G Cover) (hf:Symm (field parity) F.val)(hx:cross (parity h) (parity q)= (1:ℂ)): heart h q F=heart q h F:= by obtain ⟨s,hs⟩:=obliges F; rw [heart_by _ _ F hs,heart_by _ _ F hs]; apply Finset.sum_congr rfl; intro i _; apply Subtype.ext; have he := hf.commute (q,i) (h,i); simp only [enterp]; simpa [field,hx] using he
lemma located (i:ToneS G): offset ((P).dual i).1 = offset ((P).plain i).1:= by rcases i with ⟨_,_⟩|_ <;> rfl
lemma lapC (F:Dot G Cover) (h:Symm (field parity) F.val): run ((P).Lap F)=cycle (Kzone G) μzone (run F):= by
    funext l; unfold cycle; simp_rw [atZeroFit,Bonded.lap_at,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]; rw [integral_finsetSum]; swap
    · intro i _; apply integr; exact continuous_const.mul ((twice_cont _ _ l F).add (twice_cont _ _ l F))
    apply Finset.sum_congr rfl; intro i _; let a:=(P).dual i; let b:=(P).plain i
    change _=∫ p, (((P).fee i:ℂ)*(1/2)) * (run F ((a,p)::(b,-p)::l)+run F ((b,p)::(a,-p)::l))∂μzone
    rw [integral_const_mul, integral_add (integr _ (twice_cont a b ..)) (integr _ (twice_cont b a ..)), twice_int _ _ l _ (located i),twice_int _ _ _ _ (located i).symm, heart_sym F h (show cross (parity b) (parity a)=(1:ℂ) from (P).nob i)]; simp only [a,b,smul_eq_mul]; ring
end YM.MS.Tone
