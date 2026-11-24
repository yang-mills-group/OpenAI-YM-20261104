import YM.RegulatorIR.Warm.Self

/-! # Pencil of β at incoming and charge.P.N
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior FreeResolvent
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {P:Patch}{K:KernelChoices}{n c f:Side} {p i:ℕ}{X Y:Type}

-- sum inlet. coarse independent

def shank (Q:Layer Y X): Layer Y (X⊕Y):=fun i=>Sum.elim (fun j=> -Q i j) (ID Y i)

def knob (S:StepData c f)(v:Foot G) := shank (finer (fringe S)) v
def pepper (x:X→ℝ) : Packet X 2:=fun p=>∏ i,x (p i)
def peak (K:Packet X 2) : Ranked X:=fun p=>if h:p=2 then h.symm ▸ K else 0
lemma peak_at (K:Packet X 2): peak K 2=K:= dif_pos rfl
lemma peak_dark (K:Packet X 2){v:ℕ}(he:v≠2): peak K v=0:= dif_neg he
lemma pepper_s (x:X→ℝ): IsSym (pepper x):= fun e z=> Equiv.prod_comp e (fun i=> x (z i))
lemma pepper_fin (q:X→ℝ)(h:(Function.support q).Finite): (Function.support (pepper q)).Finite:=by refine (Set.Finite.pi (t:=fun _:Fin 2=>Function.support q) (fun _=>h)).subset fun x hx=>fun i _ hp=> hx (Finset.prod_eq_zero (mem_univ i) hp)

section Fee
variable (S:StepData c f)(z:Edge Cover)
lemma knob_f (p:Foot G): (Function.support (knob S p)).Finite:=by
 refine ((Set.Finite.image (f:=Sum.inl (β:=Foot G)) (fringe S p).hasFiniteSupport) |>.union (Set.finite_singleton (Sum.inr p))).subset ?_
 rintro (v|v) hv
 · exact Or.inl ⟨v,(show (fringe S p) v≠0 from fun h=> hv (by change -((fringe S p) v)=0;rw [h,neg_zero])),rfl⟩
 exact Or.inr (show Sum.inr v∈({Sum.inr p}:Set (Foot G⊕ Foot G)) from Classical.byContradiction fun h=>hv (by
    change ID _ p v=0; unfold ID; rw [if_neg (show p≠v from fun hv=> h (Set.mem_singleton_iff.mpr (congr_arg Sum.inr hv.symm)))]))
lemma puff (a:KFoot G→ℝ)(i:G.ColorIndex): (∑' v,knob S (z,i) v*a v)= riddle S z a i :=by
 let f:=fun v=>knob S (z,i) v*a v
 have he:Summable f:=summable_of_hasFiniteSupport ((knob_f S (z,i)).subset (fun i h=>left_ne_zero_of_mul h))
 change (∑' i,f i)= _
 rw [(he.comp_injective Sum.inl_injective).tsum_sum (he.comp_injective Sum.inr_injective)]
 change (∑' v:Foot G,-(fringe S (z,i) v)*a (.inl v)) + (∑' v:Foot G,ID (Foot G) (z,i) v*a (.inr v))=a (Sum.inr (z,i))-combo _ _
 unfold ID; simp_rw [ite_mul,one_mul,zero_mul,tsum_ite_eq',neg_mul]; rw [tsum_neg];let V:=fringe S (z,i)
 rw [tsum_eq_sum (s:=V.support)]
 · unfold combo;rw [Finsupp.linearCombination_apply,sub_eq_add_neg,add_comm];rfl
 intro n hh;rw [show fringe S _ n=0 from Finsupp.notMem_support_iff.mp hh,zero_mul]
lemma bark (a:KFoot G→ℝ)(i:G.ColorIndex): strum (pepper (knob S (z,i))) a=(riddle S z a i)^2:=by
 let K:=knob S (z,i); let v(x):=K x*a x
 have hv : (Function.support v).Finite:= (knob_f S (z,i)).subset (fun i h=>left_ne_zero_of_mul h)
 have hr : Summable (fun t : Tuple (KFoot G) 2=> ∏ i,v (t i)):=summable_of_hasFiniteSupport (pepper_fin v hv)
 let f:= (twosM (KFoot G)); unfold Prim.strum pepper noodle; rw [← f.tsum_eq]; simp_rw [← Finset.prod_mul_distrib];rw [← puff, pow_two]
 let Y(z: KFoot G × KFoot G):=v z.1*v z.2
 have ht(z) : (∏ i,v (f z i))=Y z:=by rw [Fin.prod_univ_two];rfl
 have hy: Summable Y:= (f.summable_iff.mpr hr).congr ht
 change (∑' p, ∏ i,v (f p i))= _
 simp_rw [ht]; rw [hy.tsum_prod]; unfold Y; simp_rw [tsum_mul_left,tsum_mul_right]; rfl

def seatQ (G:Gauge)(v:Edge Cover): Packet (KFoot G) 2:= (-(S.kernel.penalty)/2:ℝ) • ∑ i:G.ColorIndex,pepper (knob S (v,i))
lemma seatSym : IsSym (seatQ (G:=G) S z):=symmetric_scale (symmetric_sum (fun _ _=> pepper_s _)) _
variable (h:S.patch.Branches S.kernel G)
include h
lemma read_hess (a:KFoot G→ℝ): strum (seatQ S G z) a= -1*coeff 2 (tale (flank (opi S Clocks.flat z) a)):=by
 rw [burnM S z h]; unfold seatQ; rw [strum_tilt];
 have hf(i:G.ColorIndex): Bounded (pepper (knob S (z,i))):= pepper_fin _ (knob_f S (z,i))
 unfold Prim.strum;simp_rw [Finset.sum_apply,sum_mul];rw [Summable.tsum_finsetSum (fun i _=> by
    exact summable_of_hasFiniteSupport ((hf i).subset (fun t ht=> left_ne_zero_of_mul ht)))];
 simp_rw [show ∀ i, (∑' x,pepper (knob S (z,i)) x*noodle a x)=_ from fun i=> bark S z a i]
 rw [EuclideanSpace.norm_sq_eq]; simp_rw [Real.norm_eq_abs, sq_abs]; ring

lemma pivot_s : standby h z 2= peak (seatQ S G z):=by
 have hp:= boosted h z;have ht: Satin (peak (seatQ S G z)):=by
                                                                          intro i; unfold peak; split
                                                                          next H=> subst i; exact seatSym S z
                                                                          next h=> exact symmetric_zero
 refine guessed (hp.scope_ _) (fun i hi=> le_trans ?_ (Nat.le_refl (2+0))) (hp.smooth _) ht (fun v=>?_)
 · by_contra! hv;rw [peak_dark _ (show i≠2 by omega)] at hi;contradiction
 rw [hp.figures v (by decide)]; unfold drums; rw [Finset.sum_eq_single 2];
 · rw [peak_at]; exact (read_hess S z h v).symm
 · intro b _ h; rw [peak_dark _ h,strum_zero]
 simp
end Fee
end YM.RegulatorIR.Warm
