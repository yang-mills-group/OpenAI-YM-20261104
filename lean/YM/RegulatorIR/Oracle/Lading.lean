import YM.RegulatorIR.Oracle.Strips
import YM.Push.FREE_RESOLVENT.Metric

/-! Adapt exact Row receipts. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry
open Pert.Bulk (Market sep)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {X Y A B C V J K :Type} {S T U:Side→Type}
variable (W:Quarry X A S) (F:Quarry Y B T) (D:Quarry V C U) {p:Side} {σ α:ℝ}

def lading (M:Row A B):Layer X Y:= fun x y=> Pert.Bulk.plain M (W.toFull x) (F.toFull y)
lemma lade_eq (M:Row A B)(x:X)(y:Y): lading W F M x y = M (W.cabin x) (F.cabin y) (F.boom y-W.boom x):=rfl
lemma ladingW (M:Row A B):Albedo W F (lading W F M) := by intro i j d; rw [lade_eq,lade_eq,cargos,cargos,places,places];rw [add_sub_add_left_eq_sub]
lemma lading_f {p:Side}(y:Y): F.markedP p (F.swrap p y)= (wrap p (F.boom y),F.cabin y):=(F.markedP p).apply_symm_apply _
lemma ports_of {g:Y →ℝ}(y:Y)(p:Side): Stalk.collect (F.swrap p) g (F.swrap p y)= ∑' z:Cover, if wrap p z=wrap p (F.boom y) then g (F.toFull.symm (z,F.cabin y)) else 0:=by
 let Z:= {z:Cover// wrap p z= wrap p (F.boom y)}
 let E : Z ≃ Stalk (F.swrap p) (F.swrap p y):= Equiv.ofBijective (fun x=>⟨F.toFull.symm (x.val,F.cabin y),by rw [swrap,cabin,boom,F.toFull.apply_symm_apply];simp [x.property,cabin];rfl⟩) ⟨fun x y h=>Subtype.ext (Prod.ext_iff.mp (F.toFull.symm.injective (Subtype.mk.inj h))).1,fun i=>by
    obtain ⟨z,hz⟩:=i; obtain ⟨hx,h⟩:= Prod.mk.inj ((F.markedP p).symm.injective hz); refine ⟨⟨F.boom z,hx⟩,?_⟩; apply Subtype.ext;dsimp only; rw [← h];exact F.toFull.symm_apply_apply _⟩
 unfold Stalk.collect; rw [← E.tsum_eq];
 convert (tsum_subtype (f:=fun z=>g (F.toFull.symm (z,F.cabin y))) {z:Cover|wrap p z=wrap p (F.boom y)}) using 1 <;> first|rfl|exact tsum_congr (fun i=> by simp [Set.indicator]) 
lemma ledger_lade [Fintype B] (M:Row A B)(n:Side): ledgerRow W F (lading W F M) n=(M.acts n).submatrix (W.markedP n) (F.markedP n):=by
 ext1 i j
 obtain ⟨x,rfl⟩:= (show Surjective (W.swrap n) from fun i=>⟨_,W.both _ i⟩) i
 obtain ⟨y,rfl⟩:=(show Surjective (F.swrap n) from fun i=> ⟨_,F.both _ i⟩) j
 rw [ledger_at W F _ (ladingW W F M) x,ports_of F, Matrix.submatrix_apply,lading_f,lading_f]
 apply Eq.trans _ (Pert.Bulk.matches_plain M (W.toFull x) (wrap n (F.boom y),F.cabin y)); apply tsum_congr;intro a
 simp only [Pert.Bulk.plain,lading]; rw [F.toFull.apply_symm_apply]
lemma roots [Fintype B]{M:Row A B}(h:M.strip σ α):chestE W F σ (lading W F M) ((Fintype.card B:ℝ≥0∞)*ENNReal.ofReal α):=by
 intro x
 let f (y:Y):= ‖lading W F M x y‖ₑ*liftsE (W.boom x) (F.boom y) σ
 unfold quota; change (∑'y,f y)≤_
 let i:= W.cabin x;let a:= W.boom x;let Q:= (Equiv.prodComm B Cover).trans ((Equiv.prodCongr (Equiv.addRight a) (Equiv.refl B)).trans F.toFull.symm)
 have he (j:B)(b:Cover) : f (Q (j,b))= ENNReal.ofReal (Real.exp (σ*size b)* ‖M i j b‖):= by
   unfold f liftsE; rw [lade_eq,show Q (j,b)=F.toFull.symm (b+a,j) from rfl]
   simp_rw [boom,cabin,Equiv.apply_symm_apply]; change ‖M i j (b+a-a)‖ₑ * _= _
   rw [add_sub_cancel_right, ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm, mul_comm];
   change ENNReal.ofReal (Real.exp (σ*sep a (b+a))) * _=_
   rw [Pert.Bulk.sep_comm,Pert.Bulk.sep,add_sub_cancel_right]
 rw [← Q.tsum_eq, ENNReal.tsum_prod (f:=fun x t=> f (Q (x,t))), tsum_fintype]
 apply le_trans ?_ (le_of_eq (show (∑ _:B,ENNReal.ofReal α)=_ from by simp))
 refine Finset.sum_le_sum fun i _=>?_; simp_rw [he]
 have hh:= h (W.cabin x) i;rw [← ENNReal.ofReal_tsum_of_nonneg hh.1 hh.2.1]; exact ENNReal.ofReal_le_ofReal hh.2.2

open Work.F08
lemma lading_rev (M:Row A B): lading F W (transRows M)=Function.swap (lading W F M):=by ext1 i;ext1 j; simp only [lade_eq,Function.swap,transRows];rw [neg_sub]
lemma fond [Fintype A][Fintype B](M:Row A B)(h:M.strip σ α): FundE W F σ (lading W F M):=by
 let X:= Fintype.card A;let Y:= Fintype.card B;let Z:= ENNReal.ofReal α
 refine ⟨(X+Y:ℝ≥0∞)*Z,by unfold Z;finiteness,(roots W F h).toll (mul_le_mul_left (le_add_self) _),?_⟩
 rw [← lading_rev]; exact (roots F W (Work.F08.strip_trans h)).toll (mul_le_mul_left (le_self_add) _)
-- converse row encoding. weight conversion no color factor in this direction!
def cargo (K:Layer X Y): Row A B:= fun i j z=> K (W.toFull.symm (0,i)) (F.toFull.symm (z,j))
lemma unwind {K: Layer X Y}(h:Albedo W F K) : lading W F (cargo W F K)=K:=by
 ext1 i;ext1 j; rw [lade_eq];
 let d:= -(W.boom i)
 have hv:W.shiftB d i=W.toFull.symm (0,W.cabin i):= W.toFull.injective (by rw [W.to_shift]; simp [d])
 have ht:F.shiftB d j=F.toFull.symm (F.boom j-W.boom i,F.cabin j):= F.toFull.injective (by rw [F.to_shift];simp [d,sub_eq_add_neg,add_comm])
 unfold cargo; rw [← hv,← ht]; exact h ..
lemma cargoW {L:Layer X Y}{c:ℝ≥0∞}(h:chestE W F σ L c)(hc:c≠⊤): (cargo W F L).strip σ c.toReal:=by
 intro i j; let x:=W.toFull.symm (0,i)
 let p(z:Cover):=F.toFull.symm (z,j); have hp:Injective p:= fun i j' h=> Prod.mk.inj (F.toFull.symm.injective h)|>.1
 let g(z:Cover):= Real.exp (σ*size z)*‖cargo W F L i j z‖
 have hh(z):0≤g z:=by unfold g; positivity
 have he(z):ENNReal.ofReal (g z)=‖L x (p z)‖ₑ*liftsE (W.boom x) (F.boom (p z)) σ:=by
    unfold g;rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm,liftsE,Pert.Bulk.sep_comm (W.boom x)] -- hidden g, liftsE
    unfold Quarry.boom p x Pert.Bulk.sep; simp; exact mul_comm (ENNReal.ofReal (Real.exp (σ*size z))) _
 have ht:(∑'z:Cover,ENNReal.ofReal (g z))≤ c:=by rw [tsum_congr he]; exact (quota_restrict p hp (L x) (fun v=> liftsE (W.boom x) (F.boom v) σ)).trans (h x)
 have hv : Summable g:= (ENNReal.summable_toReal (f:=fun z=> ENNReal.ofReal (g z)) (ne_top_of_le_ne_top hc ht)).congr fun z=> ENNReal.toReal_ofReal (hh z)
 refine ⟨hh,hv,?_⟩; rw [← ENNReal.ofReal_tsum_of_nonneg hh hv,← ENNReal.ofReal_toReal hc] at ht; exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp ht
end YM.RegulatorIR.Oracle
