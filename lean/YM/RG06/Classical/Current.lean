import YM.RG06.Classical.Veil

/-!
# Actual nonlinear classical jet obstruction, transverse and triangular
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Labels Analysis Continuum Tensor Vectorial
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G:Gauge}{d n:ℕ}

def scene(g:ℝ)(A:Connection G)(b:Axis):Section G:=∑i:Axis,covariant g A i (curvature g A i b)
lemma Good_sum {I:Type*}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](s:Finset I)(f:I→E4→E)(h:∀i∈s, Good (f i)):Good (∑i∈s,f i):=by rw [show (∑i∈s,f i)=(fun x=>∑i∈s,f i x) from funext fun _=>Finset.sum_apply ..]; exact ContDiff.sum h
lemma scenical (g:ℝ)(A:Connection G)(h:Smooth A)(b:Axis): Good (scene g A b):=Good_sum _ _ fun i _=>Smooth.connection g A h i _ (Smooth.F g A h _ b)
lemma vanquish (g:ℝ)(A:Connection G)(h:Smooth A):
    (∑ b:Axis,covariant g A b (scene g A b))=0:=by
 let K(i b:Axis):=curvature g A i b
 have he(b:Axis): covariant g A b (scene g A b)=∑i:Axis,covariant g A b (covariant g A i (K i b)):=by
    have hp:=cov_lincombo (I:=Axis) g A Finset.univ (fun _=> 1) (fun i:Axis=>covariant g A i (K i b)) b (fun i _=>Smooth.connection g A h i _ (Smooth.F g A h i b))
    simp only [one_smul] at hp; exact hp
 let F(i j:Axis):=covariant g A i (covariant g A j (K j i))
 have hp(i j:Axis): F i j= - F j i :=by
   have ht:covariant g A i (covariant g A j (K j i))=covariant g A j (covariant g A i (K j i)):=by
      funext x; rw [← sub_eq_zero, commute g A h (K j i) (Smooth.F g A h j i)]
      unfold K; rw [skew g A i j,map_neg,bracket_self,neg_zero,smul_zero]
   have hf(i:Axis)(a:Section G):covariant g A i (-a)= -covariant g A i a:=by
      unfold covariant; rw [par_neg, show bracket (A i) (-a)= - bracket (A i) a by funext x; simp [bracket],smul_neg];abel
   unfold F; rw [ht, show K j i = -K i j from funext (skew g A i j), hf,hf]
 simp_rw [he]
 let T:=∑i:Axis,∑ b:Axis,F i b
 have hx:T= -T:=by
     unfold T;conv_lhs=>rw [Finset.sum_comm]
     rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun b _=> hp b i
 change T=0; apply smul_right_injective _ (by norm_num : (2:ℝ)≠0); dsimp only; rw [two_smul]; conv_lhs=>arg 1; rw [hx]
 simp

def notes(g:ℝ)(A:Connection G)(b:Axis):Section G:=∑i:Axis,(
  g • par i (bracket (A i) (A b)) + g • bracket (A i) (curvature g A i b))
lemma Good_notes (g:ℝ)(A:Connection G)(h:Smooth A)(b:Axis):Good (notes g A b):=Good_sum _ _ (fun i _=> ContDiff.add (ContDiff.const_smul g (((h i).mark (h b)).par _)) (ContDiff.const_smul g ((h i).mark (Smooth.F g A h i b))))
lemma linear_scene (g:ℝ)(A:Connection G)(h:Smooth A)(b:Axis): scene g A b= MaxwellOp A b+notes g A b:=by
 unfold scene MaxwellOp notes; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _;
 have hf:Good (par i (A b)+-par b (A i)):=ContDiff.add ((h b).par i) (ContDiff.neg ((h i).par b))
 rw [covariant]; conv_lhs=> arg 1; rw [curvature,par_add (g:=g • bracket (A i) (A b)) hf (ContDiff.const_smul g ((h i).mark (h b))),par_scale _ ((h i).mark (h b))];
 rw [sub_eq_add_neg,add_assoc]

private lemma brackets_add {a b c:Section G}:bracket (a+b) c=bracket a c+bracket b c:=funext fun _=>by simp [bracket]
private lemma brackets_hi {a b c:Section G}:bracket a (b+c)=bracket a b+bracket a c:=funext fun _=>by simp [bracket]

lemma Secret.sum {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{I:Type*}(s:Finset I){f:I→E4→E}(h:∀i∈s,Secret d (f i)):Secret d (∑i∈s,f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact Secret.zero d
 | insert a t ht H=> rw [Finset.sum_insert ht]; exact (h _ (Finset.mem_insert_self ..)).add (H (fun i hi=>h _ (Finset.mem_insert_of_mem hi)))

lemma curvature_leans (g:ℝ){A B:Connection G}(h:Smooth A)(hB:∀i,Level (n+2) (B i))(i j:Axis): Secret (n+1) (curvature g (A+B) i j-curvature g A i j):=by
 have ht(a):=Secret.vis (hB a)
 have htA(a):= (hB a).smooth
 unfold curvature; simp only [Pi.add_apply, par_add (h _) (htA _), brackets_hi,brackets_add,smul_add,neg_add_rev]
 rw [show (par i (A j)+par i (B j)+(-par j (B i)+ -par j (A i))+ (g • bracket (A i) (A j)+ g • bracket (B i) (A j)+(g • bracket (A i) (B j)+g • bracket (B i) (B j)))) - (par i (A j)+-par j (A i)+g • bracket (A i) (A j))=(par i (B j)+(-1:ℝ) • par j (B i))+(g • bracket (B i) (A j)+g • bracket (A i) (B j)+g • bracket (B i) (B j)) from (by rw [neg_one_smul];abel)]
 exact (((ht _).descend _).add (((ht _).descend _).scale _)).add (((((ht _).bracket_legal (h _)).scale _).add ((Secret.bracket_even (h _) (ht _)).scale _)|>.add (((ht _).bracket_legal (htA _)).scale _)).low (Nat.le_succ _))

lemma memo (g:ℝ){A B:Connection G}(h:Smooth A)(e:∀i, Level (n+2) (B i))(b:Axis):Secret (n+1) (notes g (A+B) b-notes g A b):=by
  have hB(i):= (e i).smooth
  have ht i:= Secret.vis (e i)
  unfold notes; rw [← Finset.sum_sub_distrib];apply Secret.sum _ _; intro i _
  simp only [Pi.add_apply,brackets_add, brackets_hi]
  have hs:=Smooth.F g A h i b
  let F:=curvature g A i b
  let G':=curvature g (A+B) i b
  let C:= bracket (A i) (A b)
  let P:= bracket (B i) (A b)
  let Q:= bracket (A i) (B b)+bracket (B i) (B b)
  have hA':Smooth (A+B):= fun i=>ContDiff.add (h i) (hB i)
  have hp:Secret (n+2) P:=(ht i).bracket_legal (h b)
  have hv: Secret (n+2) Q:= (Secret.bracket_even (h _) (ht _)).add ((ht _).bracket_legal (hB _))
  change Secret _ (g • par i (C+P+Q)+g • (bracket (A i) G'+ bracket (B i) G')-(g • par i C+g • bracket (A i) F))
  rw [show bracket (A i) G'=bracket (A i) F + bracket (A i) (G'-F) from (by rw [←brackets_hi,add_sub_cancel]), add_assoc C P Q, par_add (g:=P+Q) (Good.mark (h _) (h _)) (hp.add hv).good,smul_add,smul_add,smul_add]
  rw [show ∀u v w x y:Section G,u+v+(w+x+y)-(u+w)=v+x+y from fun _ _ _ _ _=>by abel]
  exact ((((hp.add hv).descend _).scale _).add ((Secret.bracket_even (h _) (curvature_leans g h e i b)).scale _)).add ((((ht _).bracket_legal (Smooth.F g (A+B) hA' _ _)).scale _).low (Nat.le_succ _))


lemma maxwell_add (A B:Connection G)(h:Smooth A)(hh:Smooth B)(b:Axis):
    MaxwellOp (A+B) b= MaxwellOp A b+MaxwellOp B b:=by
 rw [maxwell_value A h, maxwell_value B hh,maxwell_value (A+B) (fun i=>ContDiff.add (h i) (hh i))];
 simp only [Pi.add_apply,lap_add (h _) (hh _),par_add (h _) (hh _),Finset.sum_add_distrib,par_add (f:=∑i:Axis,par i (A i)) (g:=∑i:Axis,par i (B i)) (Good_sum _ _ (fun i _=>(h i).par i)) (Good_sum _ _ (fun i _=>(hh i).par i))]; abel
lemma maxwell_level(B:Connection G)(h:∀i,Level (n+2) (B i))(b:Axis):Level n (MaxwellOp B b):=by unfold MaxwellOp; exact Level.sum _ _ fun i _=> (Level.sub ((h b).advance i) ((h i).advance b)).advance i
lemma report (g:ℝ){A B: Connection G}(h:Smooth A)(e:∀i,Level (n+2) (B i))(b: Axis)(k:ℕ)(hk:k≤n):
    part k (scene g (A+B) b)= part k (scene g A b) + if k=n then MaxwellOp B b else 0:=by
 have hB: Smooth B:=fun i=>(e i).smooth
 have hAB(i):= (show Good ((A+B) i) from ContDiff.add (h i) (hB i))
 have hm(T:Connection G)(hT:Smooth T):Good (MaxwellOp T b):=by
    rw [maxwell_value T hT]; exact ContDiff.sub (GoodLap (hT b)) (Good.par (Good_sum _ _ (fun i _=>(hT i).par i)) b)
 rw [linear_scene g _ hAB,linear_scene g A h, part_add (hm _ hAB) (Good_notes ..),part_add (hm _ h) (Good_notes ..),maxwell_add A B h hB, part_add (hm _ h) (hm B hB)]
 have he:= (memo g h e b).veiled k (Nat.lt_succ_of_le hk)
 have hv: part k (notes g (A+B) b)=part k (notes g A b):=by
   apply sub_eq_zero.mp
   rw [sub_eq_add_neg,← neg_one_smul ℝ (notes g A b),part_add (u:=(-1:ℝ) • notes g A b) (f:=notes g (A+B) b) (Good_notes ..) (ContDiff.const_smul (-1:ℝ) (Good_notes g A h b)),part_scale,neg_one_smul,←sub_eq_add_neg] at he; exact he
   all_goals first | exact Good_notes g A h b | exact hAB
 rw [hv,add_right_comm]; congr 1; split
 next he=> subst he; exact part_level (maxwell_level B e b)
 next he=> exact part_spill (maxwell_level B e b) he
 all_goals first | exact hAB | exact h

def data(g:ℝ)(A:Connection G)(n:ℕ): Axis→E4→G.Color:=fun b=>part n (scene g A b)

theorem triangular (g:ℝ)(A:Connection G)(h:Smooth A)(v:Taylor G (n+1))(k:ℕ)(hk:k≤n):
    data g (A+v.value) k = data g A k+(if k=n then offer n v else 0):=by
   funext b
   unfold data; rw [report g h (fun i:Axis=>show Level (n+2) (v.value i) from Level.tax ..) b k hk]; split <;>rfl
lemma law (g:ℝ)(A:Connection G)(h:Smooth A):
    (∑ b:Axis,par b (scene g A b))=∑ b:Axis,(-g) • bracket (A b) (scene g A b):=by
 have he:=vanquish g A h; simp_rw [covariant,Finset.sum_add_distrib] at he
 exact (eq_neg_of_add_eq_zero_left he).trans (by rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [←neg_smul])

/-- The crucial transverse constraint with the lower equations already imposed, at center
zero in the chosen gauge. Needed for `report` shifts to be solvable along whole tower without
a physical new assumption. Inputs are static orders of a connection, not a state.
-/
lemma allegiance (g:ℝ)(A:Connection G)(h:Smooth A)(k:ℕ)(H:∀ i<k,data g A i=0): Vectorial k (data g A k):=by
 constructor; intro i; exact rate_part ..
 unfold data; rcases k with _|k
 · exact Finset.sum_eq_zero fun i _=> Level.bottom (rate_part ..) _
 have hp(b:Axis):Secret (k+1) (scene g A b):=⟨scenical g A h b,fun i hi=>congr_fun (H i hi) b⟩
 simp_rw [part_par _ (scenical g A h _)]; rw [← part_sum _ _ (fun i (_:i∈(Finset.univ:Finset Axis))=> (scenical g A h i).par i),law g A h]
 exact (Secret.sum _ (f:=fun b=> (-g) • bracket (A b) (scene g A b)) (fun i (_:i∈(Finset.univ:Finset Axis)) => (Secret.bracket_even (h i) (hp i)).scale _)).veiled k (Nat.lt_succ_self _)
end YM.RG06.ClassicalOn
