import YM.X.Dial.Flex
/-!
# Period self boost. K commutation (no continuum rotational assertion).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Dial
open Lattice Wilson Pert.Orb Next.Rank Normal MvPolynomial Function Stems Filter MeasureTheory Set Metric Finset Interval Hinge
open scoped Topology ContDiff BigOperators Pointwise
variable {R:Type*} [AddCommGroup R][One R]{G:Gauge}{n:Side}(s:Signed)
lemma step_s (i:Axis): s.act (step (S:=R) i)= if s.flip i then -step (s.perm i) else step (s.perm i):= by rw [←Step.vec_pos i,←Step.vec_rotate]; simp [Step.rotate,posDir,Step.vec]
lemma lap_s (f:Site n→ℝ)(x:Site n): lap (f ∘ s.act) x=lap f (s.act x):= by unfold lap; apply Fintype.sum_equiv s.perm; intro i; simp only [comp_apply,Signed.act_add,Signed.act_sub,step_s]; split<;> first|rfl|(rw [← sub_eq_add_neg,sub_neg_eq_add,add_comm])
lemma green_action (x:Site n): green (s.act x)=green x:= by
    let f:= green (n:=n); let g:= f ∘ s.act; have he(p): lap g p= lap f p:= by unfold g;rw [lap_s]; change lap (fun z=> (Pert.Full.toroid z).re) _= _; unfold f green; rw [lap_shift, lap_shift]; simp only [show (s.act p=0)=(p=0) from propext (by nth_rw 1 [← Signed.act_zero (R:=Per n) s]; exact s.act_injective.eq_iff)]
    have hh(p:Site n): (g-f) p=(g-f) 0:= harmonic_const _ (fun x=> by
       have ht(i : Axis):∑ i:Axis, ((g-f) (x+step i)+(g-f) (x-step i)- (2:ℝ)*(g-f) x)=(lap g x - lap f x):= by
            unfold lap; rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; simp only [Pi.sub_apply,two_smul]; ring
       rw [ht 0,he x,sub_self]) _ _
    apply sub_eq_zero.mp; refine (hh x).trans ?_; change green (s.act (0:Site n))- _ =0; rw [Signed.act_zero]; exact sub_self _
lemma dev_s(x y:Jam n G): dev (loc s x) (loc s y)=dev x y:= by
   unfold dev; have e(i:Jam n G):(loc s i).1.2=s.perm i.1.2:= by unfold loc landing; unfold Step.used; split <;> rfl
   rw [e,e]; by_cases h:y.1.2=x.1.2; swap; · simp [s.perm.injective.eq_iff,h]
   simp only [loc, h,and_true,true_and]
   split
   next=>
     rw [show (landing s y.1).1-(landing s x.1).1=s.act (y.1.1-x.1.1) by cases hx:s.flip x.1.2<;>simp [landing,Step.rotate,Step.used,posDir,h,hx]]; exact green_action ..
   rfl
lemma rot_sale : scope (reserve (R:=Per n) s) (sale (G:=G))=sale:= by
    ext1; funext x y; obtain h | h:= em (y.1.2=x.1.2); set z:ℂ:= (digit s x.1.2:ℂ); have he:z*z=1:= by unfold z digit;split_ifs<;>push_cast<;>ring
    all_goals simp only [scope,sale,reserve,treats,Finsupp.linearCombination_single, Pi.smul_apply,smul_eq_mul,dev_s]
    · change (digit s y.1.2:ℂ) * (z * _) =_; rw [h]; rw [show (digit s x.1.2:ℂ)=z from rfl,← mul_assoc,he,one_mul]
    simp [dev,h];
lemma milk_relay (p:poly (Jam n G)): milk sale (relay s p)=relay s (milk sale p):= by rw [relay,prepared,rot_sale]
lemma cover_s : let Q:= scopedK (sale (n:=n) (G:=G)) (0:Site n); scope (reserve (R:=ℤ) s) Q= Q:= by -- fix whitespace
    intro Q; ext1; funext x y; simp only [scope,treats,reserve,Finsupp.linearCombination_single, Pi.smul_apply]
    have ht (x:Hair G) : place (0:Site n) (loc s x)=loc s (place (0:Site n) x):= by cases h:s.flip x.1.2<;>simp [loc,Stems.place,west,h,landing,Step.rotate,Step.used,posDir]
    change (digit s y.1.2:ℂ) • ((digit s x.1.2:ℂ) • Q.cov (loc s x) (loc s y)) = _
    have he (i j:Hair G): Q.cov i j=sale.cov (place (0:Site n) i) (place (0:Site n) j):= (self_thermal ..).symm
    rw [he,he,ht,ht]
    have hw:= congr_arg (fun P:Symmetric (Jam n G)=> P.cov (place 0 x) (place 0 y)) (rot_sale s); simpa only [scope,treats,reserve,Finsupp.linearCombination_single,Pi.smul_apply] using! hw
end YM.PositionX.Dial
