import YM.WilsonCoeffUV.Vacuum.Gain.Ownership
/-!
# Pay for assigned rank-two retention in raw link representation
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power MultiNext.SignedSource MultiNext.SignedSource.Pattern
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β V :Type*}{s t t' σ A B C D E:ℝ}{L:Side}

-- tailor functional kills all affine-null tests incl Taylor norm.
variable {P: Ten ℝ (YForest G) 2}
def accountA (P:Ten ℝ (YForest G) 2)(f:Cover→ℝ): Prop:= broad f ∧ ∀ i v c,tailor P i v c f=0
lemma accountA.smul {f:Cover→ℝ}(h:accountA P f)(c:ℝ): accountA P (c•f):= ⟨broad_gain h.1 c,fun i j v=> by rw [tailor_M,h.2,mul_zero]⟩
lemma accountA.add {f g:Cover→ℝ}(b:accountA P f)(e:accountA P g)(p:Amber terrain t A P)(h:0<t): accountA P (f+g):=⟨broad.add b.1 e.1,fun i j v=> by rw [tailor_add p h i j v b.1 e.1,b.2,e.2,add_zero]⟩
lemma accountA.sub {f g:Cover→ℝ}(b:accountA P f)(e:accountA P g)(p:Amber terrain t A P)(h:0<t): accountA P (f-g):=by simpa only [neg_smul,one_smul,sub_eq_add_neg] using b.add (e.smul (-1)) p h
lemma accountA.sum {s:Finset V}{f:V→Cover→ℝ}(b:∀ i∈s,accountA P (f i))(p:Amber terrain t A P)(h:0<t): accountA P (∑ i∈s,f i):=by
    classical
    induction s using Finset.induction_on with
    | empty=> rw [Finset.sum_empty]; exact ⟨broad.const 0,tailor_zero P⟩
    | @insert i s e ih=> rw [Finset.sum_insert e]; exact (b i (Finset.mem_insert_self ..)).add (ih fun j hj=>b j (Finset.mem_insert_of_mem hj)) p h
lemma dollar (e:Aware P)(g: Amber terrain t A P)(h:0<t)(f: Cover→ℝ): accountA P (Newt.take 3 f) := by
   have hu : accountA P 1:=⟨broad.one,fun i j v=>(e i j v).1⟩
   have hg i : accountA P (chalk i):= ⟨broad.chalk i,fun j k v=> (e j k v).2.1 i⟩
   have hv i k : accountA P (chalk i*chalk k):= ⟨(broad.chalk i).mul (broad.chalk k), fun j x v=>(e j x v).2.2 i k⟩
   have he : Newt.take 3 f=∑ i∈Finset.range 3, (fun x=>Newt.piece i f (xyz x)):=funext fun i=>by simp only [Newt.take, Finset.sum_apply]
   rw [he]; refine accountA.sum ?_ g h; intro i hi; have hi:= Finset.mem_range.mp hi; interval_cases i
   · rw [show (fun x=> Newt.piece 0 f (xyz x))= f 0 • (1:Cover→ℝ) from funext fun x=>by simp [Newt.piece]]; exact hu.smul _
   · rw [show (fun x=>Newt.piece 1 f (xyz x))= ∑ i:Axis,Newt.jump f i 0 • chalk i from funext fun x=>by
         change Newt.piece (0+1) f _= _; simp [Newt.piece, chalk, xyz, mul_comm]]; apply accountA.sum _ g h; exact fun i _=>(hg i).smul _
   let U i j:= Newt.jump (Newt.jump f i) j 0
   rw [show (fun x=> Newt.piece 2 f (xyz x)) = ((1:ℝ)+1)⁻¹ • ∑ i:Axis,∑ j:Axis, U i j • (chalk i*chalk j - (basis i j) • chalk i) from ?_]
   · apply accountA.smul; apply accountA.sum _ g h; intro i _; apply accountA.sum _ g h; intro j _; exact ((hv i j).sub ((hg i).smul _) g h).smul _
   funext x; change Newt.piece (1+1) f _= _; rw [Newt.piece]; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; rw [Nat.cast_one]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [Newt.piece]
   simp only [Nat.cast_zero,zero_add,inv_one,one_mul,smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; simp only [Newt.piece,U,Pi.sub_apply,Pi.mul_apply, Pi.smul_apply,smul_eq_mul]; change chalk i x*((chalk j x-(basis i j))*_)=_; ring

-- second-order Taylor projection costs.
section
variable (M:ropes Cover (Co L (Hooks G)) (Hooks G))
def chop : Fin 2→ℕ:=![3,0]
def paneQ (M:ropes Cover (Co L (Hooks G)) (Hooks G)): Fin 2→ Roof (Hooks G) (Hooks G) 2:= fun i=> nestTake L M 1 i (chop i)
-- identity using all (x+z). fixed-second variables shifted to anchor.
omit M in
lemma drive₂ {p:YForest G}(x:Cover)(u:Axis)(j:G.ColorIndex)(g:stroll P): P (Fin.cons (waive (p.1+x) u j) ![p])= petals P p.2 u j x:= by
   let D:= g p.1 (Fin.cons (waive x u j) ![(0,p.2)])
   refine (congr_arg P ?_).trans D; ext1 i; fin_cases i; rfl
   change p=(p.1+0,_); rw [add_zero]; rfl
lemma orbitQ (h:stroll P)(ha:Aware P)(hp:Amber terrain t A P)(he:0<t)(hv:∀ x,Summable (spinJob P (paneQ M) x))(hw:∀ x,Summable (spinJob P (owns L M) x)): pump P (paneQ M)=pump P (owns L M) := by
   funext x
   let K:= Fin.consEquiv (fun _:Fin 2=>YForest G)
   let V:= (Equiv.prodComm ..).trans K
   let F:= spinJob P (paneQ M) x; let Q:= spinJob P (owns L M) x
   have hh : Summable (Q-F):= (hw x).sub (hv x);
   apply Eq.symm
   unfold pump; change _= ∑' y,F y
   apply sub_eq_zero.mp; rw [← (hw x).tsum_sub (hv x), ← V.tsum_eq (fun i=>_)];
   change ∑' z,(Q-F) (V z)=0
   have heq : Summable (fun z=> (Q-F) (V z)):=V.summable_iff.mpr hh
   rw [heq.tsum_prod]; rw [tsum_congr (g:=fun _=> (0:ℝ)) ?h,tsum_zero]
   case h =>
    intro y; let p' := y 0
    let Y (i:YForest G): Fin 2→YForest G:= Fin.cons i y
    let f (i:YForest G):= Q (Y i)- F (Y i)
    have hx : Summable (f ∘ (booths G)):= (booths G).summable_iff.mpr (heq.prod_factor y)
    change (∑' i,f i)=0
    rw [← (booths G).tsum_eq f]; change (∑' j,(f ∘ (booths G)) j)=0
    rw [hx.tsum_prod,tsum_fintype]; apply Finset.sum_eq_zero; rintro ⟨c,i⟩ _
    let u:=(p'.1:Cover); let G' z:= spring L M (waive (u+z) i c) (x 0)
    let B:= spring L M p' (x 1)
    have hY : y= ![p']:= funext fun j=> by fin_cases j; rfl
    rw [← (Equiv.addLeft u).tsum_eq (fun z=> _)]
    have ht z: f (waive (u+z) i c)= B * ((Newt.take 3 G' z)*petals P p'.2 i c z) := by
       set g':= waive (u+z) i c; have hz: P (Y g')=petals P p'.2 i c z:= by unfold Y; rw [hY]; exact drive₂ _ _ _ h
       have hx : nestTake L M 1 0 3 (Y g') (x 0)=G' z-Newt.take 3 G' z:= by unfold nestTake; rw [show ((Y g') 0).1-((Y g') 1).1=z from add_sub_cancel_left _ _]; rfl
       have hp: paneQ M 1=owns L M 1:= nest_base ..
       unfold f F Q; rw [spinJob,spinJob]; simp_rw [Fin.prod_univ_two,hp, hz, smul_eq_mul]
       change G' z * B * _ - nestTake L M 1 0 3 (Y g') _ * B * _= _
       rw [hx]; ring
    change (∑' z,f (waive (u+z) i c))=0; rw [tsum_congr ht,tsum_mul_left]; exact mul_eq_zero_of_right _ ((dollar ha hp he G').2 p'.2 i c)
end
end YM.WilsonCoeffUV.Bank
