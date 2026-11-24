import YM.RegulatorIR.Warm.Seal

/-! # Combine pre-stable carriers with stem and crop on all ranks. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y W L:Type}{e p:ℕ}
section
variable {c f:Side} (D:StepData c f) -- undeclared c f
lemma fuel_goal (H:Billed (finer (fringe (X:=G.ColorIndex) D)))(ht:Billed (Function.swap (finer (fringe (X:=G.ColorIndex) D)))) : massive (seatQ D G)=coil (warmP D.kernel.penalty (finer (fringe D))):=by
 let R:= shank (finer (fringe (X:=G.ColorIndex) D))
 ext1 x; let a:=x 0;let b:=x 1; let d:= D.kernel.penalty
 have hv(z:Edge Cover) : (seatQ D G z) x=(-d/2)*∑ i:G.ColorIndex,R (z,i) a* R (z,i) b:=by
    rw [seatQ];change (-d/2)*(∑ i:G.ColorIndex,_ : Packet (KFoot G) 2) x= _; rw [Finset.sum_apply]; apply congr_arg; apply sum_congr rfl;intro i _;exact Fin.prod_univ_two (fun j:Fin 2=>knob D (z,i) (x j))
 let p(i: Edge Cover)(v:G.ColorIndex):=R (i,v) a* R (i,v) b; obtain ⟨hP,h⟩ := shanks H ht
 have hh: Summable (fun x:Edge Cover× G.ColorIndex=> p x.1 x.2):= counts_profile h hP a b
 change (∑' z:Edge Cover,_) = (-1/2:ℝ)*(d* ∑' v:Foot G, p v.1 v.2)
 simp_rw [hv, tsum_mul_left]; rw [hh.tsum_prod]; simp_rw [tsum_fintype]; unfold p d;ring
end

section Bed
variable {P:ℝ}{A:Deck P X W}{B:Deck P Y L}{K N:Layer X X}{K':Layer Y Y}{D:Layer X Y}{Q:Layer Y X} {a:W→Prop}{v:ℝ}
variable (H: Quadratic.Bedload A B v a K K' Q D N) (hd:Billed (Function.swap D))
lemma coil_bound {T:Layer X X}(h:Billed T) : Limits (coil T) :=by
 obtain ⟨c,hc,H⟩:= billing_point h;refine ⟨_, ENNReal.mul_ne_top (show ‖(-1/2:ℝ)‖ₑ≠⊤ from enorm_ne_top) hc,fun x=>?_⟩;unfold Axial.coil;rw [enorm_mul]; exact mul_le_mul_right (H ..) _
lemma button (K:Layer X X) : offer (Embedding.inl: X↪X⊕Y) (coil K)= coil (entryK (Y:=Y) K):=by
 let p:=Embedding.inl (α:=X) (β:=Y); ext1 x
 by_cases ht:x∈Set.range (acrossT p)
 · obtain ⟨a,rfl⟩:=ht; rw [offer_eq]; rfl
 rw [offer_zero _ ht]; change 0=(-1/2)*entryK K (Y:=Y) (x 0) (x 1)
 cases h0:x 0 <;> cases h1:x 1
 next i j=>exact (ht ⟨![i,j],funext (fun k=> by fin_cases k; exact h0.symm; exact h1.symm)⟩).elim
 all_goals rw [show entryK K _ _=0 from rfl]; ring
lemma enticed {K P:Layer X X}: coil (K+P)=coil K+coil P:=by ext1 x; exact mul_add ..
lemma pair_pull {F:Layer X X}{V:Layer X Y} (h:Billed F)(_ht:Billed V)(hv:Billed (Function.swap V)) (a : Tuple Y 2):
 (∑' x:Tuple X 2,coil F x*∏ i,V (x i) (a i))=coil (lap (Function.swap V) (lap F V)) a:=by
 let H x:= V x (a 0); let K x:= V x (a 1); let f(x:Tuple X 2):= F (x 0) (x 1)*∏ i,V (x i) (a i)
 let g(i j:X):= V i (a 0)*(F i j*V j (a 1)); let F0:= twosM X
 have he: ∀ i:X×X,f (F0 i)=g i.1 i.2:=by intro i; unfold f g F0; rw [Fin.prod_univ_two]; change F i.1 i.2* (H i.1*K i.2)=H i.1*(F i.1 i.2*K i.2);ring
 have hS: Summable f:=by
    obtain ⟨c,hc,H⟩:= billing_point h
    apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_base]; apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (tallS X 2 (fun i v=> ‖V v (a i)‖ₑ) ?_))
    · rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum;intro x;unfold f; rw [enorm_mul];apply mul_le_mul' (H ..); rw [Fin.prod_univ_two,Fin.prod_univ_two,enorm_mul]
    intro i; have hf:= hv.rows (a i); simpa only [quota_base] using hf
 have hz : Summable (fun b:X×X=>g b.1 b.2):= (F0.summable_iff.mpr hS).congr he
 unfold Axial.coil;simp_rw [mul_assoc (-1/2:ℝ),tsum_mul_left];change _*(∑' x,f x)= _;apply congr_arg;rw [← F0.tsum_eq];simp_rw [he]; rw [hz.tsum_prod]; simp_rw [g, tsum_mul_left]; rfl
lemma coil_s (K:Layer Y Y)(h:Function.swap K=K) : IsSym (coil K):=by
 intro p x; have hp:=p.injective.ne (show (0:Fin 2) ≠ 1 by decide); unfold Axial.coil; apply congr_arg; change K (x (p 0)) (x (p 1))=_; generalize hv:p 0=i at *;generalize hl:p 1=j at *;fin_cases i <;> fin_cases j <;> first|rfl|contradiction|exact congr_fun (congr_fun h _) _
variable (S:GridStep A B) (hS:S.driftL=Function.swap (hoses D))(hb:Billed S.driftL)
include hb hS H hd
lemma carries (hp: Function.swap K'=K'): S.pullI (offer (firstChannel A B).native (coil K)+coil (warmP v Q))=coil K':=by
 let A₀:= firstChannel A B; let F:= flareK v Q K; let P:=flare_f H.rows.1 H.rows.2.1 H.rows.2.2.1 v; let T:= lastChannel A B -- replace
 let g(x:Tuple Y 2):= acrossT T.native x
 rw [show offer (firstChannel A B).native (coil K)=coil (entryK K) from button K,← enticed]
 have hf(x): drawing (coil F) S.driftL (List.finRange 2) (g x) = coil K' x:=by
    rw [wind_up (coil_bound P) _ hb (g x) _ (List.nodup_finRange _)]
    simp_rw [Gradient.field,show ∀ (z:Tuple (X⊕Y) 2), Gradient.covers z (g x) (List.finRange 2) from fun _ i hi=>(hi (List.mem_finRange ..)).elim, if_true,List.toFinset_finRange]; obtain ⟨ht,h'⟩:= chargedV H.rows.2.2.2.1 hd; rw [← stings H hd,← pair_pull P ht h' x]; apply tsum_congr;intro i; apply congr_arg; refine prod_congr rfl fun i' _=>?_; rw [hS];let f:=i i'; change hoses D f (.inr _) = stemY D f (x i'); cases f <;> rfl
 change crop T.native (symmetry (drawing (coil F) S.driftL _))= _
 rw [crop_clock,show crop _ (drawing (coil F) S.driftL (List.finRange 2))=coil K' from funext hf]; exact symmetric_already _ (coil_s K' hp)
end Bed
end YM.RegulatorIR.Warm
