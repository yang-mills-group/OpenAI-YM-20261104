import YM.RegulatorIR.Venture.Opposed

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Epoch
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
variable {X Z:Type} {W:X→Type}{A:(x:X)→Tariff (W x)}{L:Meter X}{F:X→ℝ≥0∞} {r s p q e k i m:ℕ}
variable {B D:(x:X)→Layer (W x) (W x)} {T U:(x:X)→ Orders (W x)}
variable (hK:Beam L A B)(ht:∀ x,Vacuum (T x))(h:∀ i j,Earlier e r i j→Workday L A (fun w=>T w i j))
include hK ht h
open VacDay
lemma v_issue (H:Touch e r p q)(he:k=0→Earlier e r p q): Workday L A (fun w=>logHeat (B w) (T w) false k p q):=by
 induction k using Nat.strong_induction_on generalizing p q with
 | _ k ih=>
    cases k with
    | zero=>
       simp_rw [logHeat_first]; by_cases hr:q=0
       · subst q;exact plain_r void_r
       simp_rw [if_neg (not_and_of_not_left _ hr)]; exact h p q (he rfl)
    | succ k=>
       simp_rw [logHeat_next]; by_cases hr:q=0
       · subst q;exact plain_r void_r
       simp_rw [if_neg (not_and_of_not_left _ hr)]; apply Workday.csmul
       have hx: Earlier e r p (q+2):=by unfold Touch Earlier at *;omega
       apply Workday.add (Workday.with_heat (ih k (by omega) (widen hx) (fun _=>hx)) hK); apply Workday.csmul; unfold Diagram.drift Diagram.carry; apply Workday.sum;intro d hd; apply Workday.sum; rintro ⟨a,b⟩ hv; by_cases hk:a*b=0
       · rcases Nat.mul_eq_zero.mp hk with hk|hk
         · subst a; simp_rw [fun w:X=> statics (e:=d.1) (B w) (ht w),(force_z ..).1];exact Workday.zeroQ
         subst b; simp_rw [fun w:X=> statics (e:=d.2) (B w) (ht w),(force_z ..).2]; exact Workday.zeroQ
       have hp: p≤e:=by unfold Touch at H;omega
       have hb:a+b=p:=Finset.mem_antidiagonal.mp hv;have hv:= Finset.mem_antidiagonal.mp hd;have hz:a≠0:=fun h=>hk (by rw [h, Nat.zero_mul]);have hg:b≠0:=fun h=>hk (by rw [h,Nat.mul_zero]);
       unfold force; apply Workday.sum; rintro ⟨i,j⟩ hj; apply Workday.with_match q i j hK (ih d.1 (by omega) (show Touch e r a (i+1) from Or.inl (by omega)) fun _=>Or.inl (by omega)) (ih d.2 (by omega) (show Touch e r b (j+1) from Or.inl (by omega)) fun _=> Or.inl (by omega))
variable (hD:Beam L A D)(H':RailDay F L A (fun i=>B i-D i))(hv:∀ x,Vacuum (U x)) (hU:∀ i j,Earlier e r i j→ Workday L A (fun w=> U w i j)) (hh:∀ i j,Earlier e r i j→ VacDay F L A (fun w=> T w i j-U w i j))
omit hK ht h
private lemma sum_cut (v:Finset Z) {T U:Z→(x:X)→Packet (W x) k}(h:∀ i∈v,VacDay F L A (fun x=>T i x-U i x)): VacDay F L A (fun x=>(∑ i∈v,T i x)-(∑ i∈v,U i x)):=by simp_rw [← sum_sub_distrib]; exact VacDay.sum _ h
private lemma tiltCut {T U:(x:X)→Packet (W x) r}(H:VacDay F L A (fun i=> T i-U i))(c:ℝ) : VacDay F L A (fun i=> c • T i-c • U i):=by simp_rw [← smul_sub]; exact H.tilts _
private lemma matting {T U T' U':(x:X)→Ranked (W x)}(hK:Beam L A B)(hD:Beam L A D)(H':RailDay F L A (fun i=>B i-D i))(h:Workday L A (fun w=>T w (p+1)))(h':Workday L A (fun w=> T' w (p+1)))(ht:Workday L A (fun w=> U w (q+1)))(hU:Workday L A (fun w=> U' w (q+1)))(he:VacDay F L A (fun w=>T w (p+1)-T' w (p+1)))(hv:VacDay F L A (fun w=>U w (q+1)-U' w (q+1)))(r:ℕ) (hs:p+q=r):VacDay F L A (fun w=>matchTwo (B w) (T w) (U w) r (p,q)-matchTwo (D w) (T' w) (U' w) r (p,q)):=by
 subst r; simp only [matchTwo, ↓reduceDIte]; apply tiltCut; simp_rw [← symmetry_sub];exact VacDay.sym (knot_v h h' ht hU he hv hK hD H')
include hK ht h hD H' hv hU hh
lemma diff_issue (H:Touch e r p q)(he:k=0→Earlier e r p q): VacDay F L A (fun w=> logHeat (B w) (T w) false k p q-logHeat (D w) (U w) false k p q):=by
 induction k using Nat.strong_induction_on generalizing p q with
 | _ k ih=>
    cases k with
    | zero=>
       simp_rw [logHeat_first]; by_cases hr:q=0
       · subst q;exact void_r
       simp_rw [if_neg (not_and_of_not_left _ hr)]; exact hh p q (he rfl)
    | succ k=>
       simp_rw [logHeat_next]; by_cases hr:q=0
       · subst q;exact void_r
       simp_rw [if_neg (not_and_of_not_left _ hr)]; apply tiltCut
       have hx: Earlier e r p (q+2):=by unfold Touch Earlier at *;omega
       simp_rw [add_sub_add_comm]; apply VacDay.add
       · unfold heating; apply tiltCut; simp_rw [← symmetry_sub]
         exact VacDay.sym (loop_v (v_issue hK ht h (widen hx) (fun _=>hx)) (v_issue hD hv hU (widen hx) (fun _=>hx)) hK hD H' (ih k (by omega) (widen hx) (fun _=>hx)))
       apply tiltCut; unfold Diagram.drift Diagram.carry; apply sum_cut; intro d hd; apply sum_cut; rintro ⟨a,b⟩ he; by_cases hk:a*b=0
       · rcases Nat.mul_eq_zero.mp hk with hk|hk
         · subst a; simp_rw [fun w:X=> statics (e:=d.1) (B w) (ht w),fun w:X=> statics (e:=d.1) (D w) (hv w),(force_z ..).1,sub_self];exact zero_r
         subst b; simp_rw [fun w:X=> statics (e:=d.2) (B w) (ht w),fun w:X=> statics (e:=d.2) (D w) (hv w),(force_z ..).2,sub_self];exact zero_r
       have hp:p ≤ e:=by unfold Touch at H;omega
       have hA:a≠0:=fun he=>hk (by rw [he, Nat.zero_mul]); have hB:b≠0:=fun he=>hk (by rw [he,Nat.mul_zero]); have hV:=Finset.mem_antidiagonal.mp hd;have hE:a+b=p:=Finset.mem_antidiagonal.mp he
       unfold force; apply sum_cut; rintro ⟨i,j⟩ hj; let t:=i+1;let u:=j+1;have he:Earlier e r a t:=Or.inl (by omega);have hh':Earlier e r b u:=Or.inl (by omega)
       exact matting (p:=i) (q:=j) hK hD H' (v_issue hK ht h (widen he) (fun _=>he)) (v_issue hD hv hU (widen he) (fun _=>he)) (v_issue hK ht h (widen hh') (fun _=>hh')) (v_issue hD hv hU (widen hh') (fun _=>hh')) (ih d.1 (by omega) (widen he) (fun _=>he)) (ih d.2 (by omega) (widen hh') (fun _=>hh')) q (mem_antidiagonal.mp hj)
-- family T i incl A any.Step
omit hD H' hv hU hh

def shedding (B:Layer X X)(T:Orders X)(e:ℕ)(r):Packet X r:=∑ i∈ Finset.range (3*e),logHeat B T false (i+1) e r
lemma restoration : Workday L A (fun i=>shedding (B i) (T i) e r):=by -- shadow remove
 apply Workday.sum; intro p _; exact v_issue hK ht h (show Touch e r e r from Or.inr ⟨rfl, le_rfl⟩) (fun h=>False.elim (by omega))
include hD H' hv hU hh
lemma restoration_t : VacDay F L A (fun i=> shedding (B i) (T i) e r - shedding (D i) (U i) e r):= sum_cut _ (fun p _=> diff_issue hK ht h hD H' hv hU hh (show Touch e r e r from Or.inr ⟨rfl,le_rfl⟩) fun h=>False.elim (by omega))
end YM.RegulatorIR.Epoch
