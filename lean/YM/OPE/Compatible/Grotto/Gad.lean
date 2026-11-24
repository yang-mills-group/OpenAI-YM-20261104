import YM.OPE.Compatible.Grotto.Gale
/-!
# nilpotent asympt upper/injectivity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics Drift
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {m:ℕ}{T:E→L[ℝ] E}{r x:ℝ}{v:E}
lemma Edit (T:E→L[ℝ] E)(x:ℝ) : Commute (Ux T x) T:=by
   unfold Commute SemiconjBy Ux; ext j; rw [byway,byway]; change _ - (x:ℝ) • _= T (T j-x • j); rw [map_sub,map_smul];rfl
lemma AltE (T:E→L[ℝ] E)(x:ℝ)(m:ℕ)(hx:0 ≤ x)(ht:x<r): ∃ C:ℝ,0≤ C∧∀ v:E,(Ux T x^m) v=0→ Hex r (tale T v) (C*‖v‖):=by
    let U:=Ux T x; induction m with
    | zero=> exact ⟨0,le_rfl,fun v hv=>by rw [show v=0 from by simpa using hv]; intro i; simp [tale]⟩
    | succ j ih=>
       obtain ⟨c,hc,H⟩:=ih; have ht':0 ≤ r-x:=sub_nonneg.mpr ht.le; let C:= 1+c*‖U‖/(r-x); have hu:0≤ c*‖U‖/(r-x):=by positivity
       refine ⟨C,(zero_le_one.trans (le_add_of_nonneg_right hu)),fun v hv=>?_⟩; rw [pow_succ,byway] at hv; let p:= tale T v
       have hP(i:ℕ): U (p i)= tale T (U v) i:=by unfold p tale; rw [← byway, ((Edit T x).pow_right i).eq,byway]
       have hh:Run (flint x) p (tale T (U v)):=by
            intro i; change (T^(i+1)) v=x • _+_; rw [pow_succ',byway,← hP]; change _= _+Ux T x _; rw [shiftUx]; change T (p i)=x • p i+ (T (p i)-x • p i); abel
       refine Run.gap ht _ hx ?_ (H (U v) hv) hh (fun i=>by simp [flint,norm_smul,Real.norm_eq_abs,abs_of_nonneg hx]) ?_
       · have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_opNorm U v) hc) (inv_nonneg.mpr ht'); apply le_trans (show c*‖U v‖/(r-x)≤ (c*‖U‖/(r-x))*‖v‖ from le_trans (by simpa only [div_eq_mul_inv] using hh) (le_of_eq (by ring))); apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _) -- hh ring
       change ‖v‖≤ _; exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right hu)
lemma Ipso (hv:(Ux T x^m) v=0)(hx:r<x)(hr:0≤r) (hh:∃ C, Hex r (tale T v) C): v=0:=by
   induction m generalizing v with
   | zero=> simpa using hv
   | succ m ih=>
       rw [pow_succ,byway] at hv; obtain ⟨c,hc⟩:=hh; have ht : Hex r (tale T (Ux T x v)) (‖Ux T x‖*c):=by
            convert! Hex.invoke (Ux T x) hc using 1; funext i; unfold tale; rw [← byway,← byway, ((Edit T x).pow_right i).eq]
       have hz:= ih hv ⟨_,ht⟩; let p:=tale T v; have hp(i:ℕ): (Ux T x) (p i)=0:=by change (Ux T x) ((T^_) v)=_; rw [← byway,((Edit T x).pow_right i).eq,byway,hz,map_zero]
       have hh: Run (flint x) p 0:=by
            intro i; rw [show p (i+1)=T (p i) by unfold p tale; rw [pow_succ',byway], show T (p i)=x • p i from sub_eq_zero.mp (hp i),Pi.zero_apply,add_zero];rfl
       exact (show p 0= _ from det hr hx hh hc)
end YM.OPE.Hark
