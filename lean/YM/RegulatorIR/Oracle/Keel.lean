import YM.RegulatorIR.Oracle.Board

/-! Covariances via quarries. Ordinary period algebra. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry
open Pert.Bulk (Market sep)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {X Y A B C V J K :Type} {S T U:Side→Type}
variable (W:Quarry X A S) (F:Quarry Y B T) (D:Quarry V C U) {p:Side}
namespace Albedo
variable {W F D}{L M:Layer X Y}{N:Layer Y V}
lemma lap (h:Albedo W F L)(hh:Albedo F D N): Albedo W D (lap L N):=by
 intro x y d; unfold Quadratic.lap; rw [← (F.shiftB d).tsum_eq]; simp_rw [h x,hh (y:=y)] -- binder name?
lemma add (h:Albedo W F L)(hh:Albedo W F M): Albedo W F (L+M):=fun i j d=>congr_arg₂ (·+·) (h i j d) (hh i j d)
lemma sub (h:Albedo W F L)(hh:Albedo W F M): Albedo W F (L-M):=fun i j d=>congr_arg₂ (·-·) (h i j d) (hh i j d)
lemma swap (h:Albedo W F L) : Albedo F W (Function.swap L):=fun i j d=> h j i d
lemma smul (h:Albedo W F L)(t:ℝ): Albedo W F (t • L) :=fun i j d=>congr_arg (t*·) (h i j d)
end Albedo

variable {L M:Layer X Y}
lemma Ledger.add (p:Side)(h:Billed L)(hp:Billed M): ledgerRow W F (L+M) p=ledgerRow W F L p+ledgerRow W F M p:=by
 ext1 x y; let g:=W.slift p x; have he (Z:Layer X Y)(h:Billed Z):Summable (fun i:Stalk (F.swrap p) y=>Z g i.val):= (quota_summable (w:=1) (fun _=>le_rfl) (h.rows g)).comp_injective (show Injective (Subtype.val : Stalk (F.swrap p) y→_) from Subtype.val_injective); exact Summable.tsum_add (he L h) (he M hp)
lemma Ledger.neg (p:Side)(L:Layer X Y): ledgerRow W F (-L) p= -ledgerRow W F L p :=by ext1 x y; change (∑' i:Stalk (F.swrap p) y, -(L _ i.val))= - (∑' i:Stalk (F.swrap p) y, L _ i.val); rw [tsum_neg]
lemma Ledger.sub (p:Side)(h:Billed L)(hp:Billed M): ledgerRow W F (L-M) p=ledgerRow W F L p-ledgerRow W F M p:=by rw [sub_eq_add_neg,Ledger.add W F p h hp.neg,Ledger.neg,sub_eq_add_neg]
lemma Ledger.smul (p:Side)(L:Layer X Y)(r:ℝ): ledgerRow W F (r • L) p=r • ledgerRow W F L p:=by ext1 x y; change (∑' i:Stalk (F.swrap p) y,r*L _ i.val)=r* _; rw [tsum_mul_left];rfl

lemma main_zero (p:Side) [DecidableEq (S p)]: ledgerRow W W (ID X) p=1:=by
 ext1 x y; let v:= W.slift p x; change (∑' i:Stalk (W.swrap p) y,ID X v i.val)= _; by_cases h:x=y
 · subst y; rw [tsum_eq_single ⟨v,W.both p x⟩];simp [Quadratic.ID]; intro z hz; apply if_neg;intro h; exact hz (Subtype.ext h.symm)
 have hp (i: Stalk (W.swrap p) y): ID X v i.val=0:=if_neg (fun he=> h ((W.both p x).symm.trans ((congr_arg _ he).trans i.property)))
 simp_rw [hp]; simp [h]
lemma Albedo.base : Albedo W W (ID X):=by intro i j d; unfold ID; simp
lemma Ledger.lap (p:Side) [Fintype (T p)] {L: Layer X Y}{N: Layer Y V}(h:Billed L)(hp:Billed N)(hn:Albedo F D N): ledgerRow W D (lap L N) p= ledgerRow W F L p*ledgerRow F D N p:=by
 ext1 x y; let v:=W.slift p x
 let g (z:Y):= L v z* ledgerRow F D N p (F.swrap p z) y
 let f(z: Stalk (D.swrap p) y):Y→ℝ:= fun i=> L v i*N i z.val
 have hz : Summable (fun t:Y × Stalk (D.swrap p) y=>f t.2 t.1):=by
   apply quota_summable (w:=1) (fun _=>le_rfl); obtain ⟨c,hc,h'⟩:=hp
   let r:= fun t:Y × Stalk (D.swrap p) y=> (t.1,t.2.val); have hv:Injective r:=fun _ _ e=> Prod.ext (congr_arg (Prod.fst : Y × V→Y) e) (Subtype.ext (congr_arg (Prod.snd : Y × V→V) e))
   exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows v) hc) ((quota_restrict r hv (fun t:Y × V=>L v t.1*N t.1 t.2) 1).trans (Billed.lap_base h' v))
 have hs i:g i=∑'z:Stalk (D.swrap p) y,f z i:=by unfold g;rw [ledger_at F D N hn, Stalk.collect, ← tsum_mul_left]
 have ht:Summable g:=by rw [show g= _ from funext hs];exact hz.prod
 rw [Matrix.mul_apply]; change (∑' z: Stalk (D.swrap p) y,∑' i,f z i)=_
 rw [← (show Summable (uncurry f) from hz.prod_symm).tsum_comm,← tsum_congr hs,← Stalk.collected_sum (F.swrap p) ht, tsum_fintype]; apply Finset.sum_congr rfl; intro i _; unfold Stalk.collect; simp_rw [g, show ∀ x:Stalk (F.swrap p) i,F.swrap p x.val=i from fun v=> v.property,tsum_mul_right];rfl

-- inverse paths for a and b. No orientation. prove both projections by parametrizing fiber with Cover.
def stroll (p:Side)(x:X): Cover≃ (Stalk (W.swrap p) (W.swrap p x)):=by
 apply Equiv.ofBijective (fun v=> ⟨W.shiftB (p.val • v) x,(W.periodic x v p).symm⟩); constructor
 · intro i j h; have ht:=congr_arg (fun z:Stalk (W.swrap p) (W.swrap p x)=>W.boom z.val) h; dsimp only at ht; rw [places,places] at ht
   exact smul_right_injective Cover p.property.ne' (add_right_cancel ht)
 intro i; obtain ⟨z,h⟩:= W.fibers i.property.symm; exact ⟨z,Subtype.ext h.symm⟩
lemma Ledger.rev (p:Side)(h:Albedo W F L): ledgerRow F W (Function.swap L) p= (ledgerRow W F L p).transpose:=by
 ext1 y x; obtain ⟨x,rfl⟩:= (show Surjective (W.swrap p) from fun i=> ⟨_,W.both p i⟩) x; obtain ⟨y,rfl⟩:=(show Surjective (F.swrap p) from fun i=> ⟨_,F.both p i⟩) y
 rw [ledger_at F W _ h.swap, Matrix.transpose_apply,ledger_at W F _ h]; unfold Stalk.collect
 rw [← (stroll W p x).tsum_eq,← ((Equiv.neg Cover).trans (stroll F p y)).tsum_eq]
 apply tsum_congr;intro i; change L (W.shiftB (p.val • i) x) y = L x (F.shiftB (p.val • (-i)) y)
 rw [← h x (F.shiftB (p.val • (-i)) y) (p.val • i)]; congr 1
 apply F.toFull.injective; rw [F.to_shift,F.places,F.cargos]; rw [smul_neg]; simp; rfl

-- authority on arbitrary periodic arrays
variable {n:Side}
section
variable [Fintype (T n)]
lemma transmit (L:Layer X Y) (a:T n→ℝ)(x:X) (h:Billed L)(he:Albedo W F L) : (ledgerRow W F L n *ᵥ a) (W.swrap n x)=∑'i,L x i*a (F.swrap n i):=by
 let f(i:Y):= L x i*a (F.swrap n i)
 have hs: Summable f:=by
    let M:= Finset.univ.sup (fun i:T n=> ‖a i‖ₑ)
    apply quota_summable (w:=1) (fun _=>le_rfl); apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows x) (show M ≠ ⊤ from lt_top_iff_ne_top.mp (Finset.sup_lt_iff (by simp)|>.mpr fun i _=>by finiteness)))
    rw [quota_base,quota_base,← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum;intro i;unfold f; rw [enorm_mul];exact mul_le_mul_right (Finset.le_sup (s:=Finset.univ) (f:=fun i:T n=> ‖a i‖ₑ) (Finset.mem_univ _)) _
 rw [← Stalk.collected_sum (F.swrap n) hs,tsum_fintype];apply Finset.sum_congr rfl;intro i hi;change ledgerRow W F L n (W.swrap n x) i*a i=_; rw [ledger_at W F L he]; simp_rw [Stalk.collect,f, show ∀ j:Stalk (F.swrap n) i,F.swrap n j.val=i from fun v=>v.property,tsum_mul_right]
end
end YM.RegulatorIR.Oracle
