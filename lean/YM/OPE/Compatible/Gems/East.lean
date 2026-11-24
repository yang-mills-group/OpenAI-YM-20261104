import YM.OPE.Compatible.Gems.Beam
/-! # Factor estimates for first three cumulants. Minkowski acceleration. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset Matrix
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav
variable {X Y:Type*}{t s u x y ε:ℝ}{k:ℕ}[MeasurableSpace X]
variable {A B C D F:price}
variable {μ:Measure X} {p q r p' q' r' :X→ℝ}
section
variable (μ) (p q r)
lemma Swap2 : κ2 μ p q=κ2 μ q p:=by unfold κ2; rw [mul_comm p q,mul_comm (a_ μ p)]
lemma Order3 : κ3 μ p q r=κ3 μ p r q ∧ κ3 μ p q r=κ3 μ q p r:=by
       unfold κ3; constructor
       · rw [mul_right_comm p, mul_comm q]; ring
       rw [mul_comm p q]; ring
lemma beak3 : κ3 μ p q r=κ2 μ (p*q) r-κ2 μ p r*a_ μ q-a_ μ p*κ2 μ q r:=by unfold κ3 κ2;ring
end
section
variable [IsProbabilityMeasure μ]
abbrev Duo (v s:ℝ):= 2*v*s
lemma xBin (hp:Fault μ 2 p t)(hq:Fault μ 2 q s): ‖κ2 μ p q‖≤ Duo t s :=by
       unfold κ2; refine (norm_sub_le ..).trans ((add_le_add ((hp.double (i:=1) hq zero_lt_one).pays le_rfl) (b:=t*s) (d:=t*s) ?_).trans_eq ?_); · rw [norm_mul]; exact mul_le_mul (hp.pays one_le_two) (hq.pays one_le_two) (norm_nonneg _) hp.pos
       unfold Duo;ring
abbrev trioK (t s u:ℝ):= 6*t*s*u
lemma xTern (hp:Fault μ 4 p t)(hx:Fault μ 4 q s)(hr:Fault μ 4 r u) : ‖κ3 μ p q r‖ ≤ trioK t s u:=by
        have hf:= hp.mono (show 2≤4 by decide) le_rfl; have hq:= hx.mono (show 2≤4 by decide) le_rfl; have hh:= hr.mono (show 2≤4 by decide) le_rfl; rw [beak3]; apply (norm_sub_le ..).trans; rw [norm_mul]; refine (add_le_add ((norm_sub_le ..).trans (add_le_add (xBin (hp.double hx (show 0 < 2 by decide)) hh) (d:= Duo t u*s) ?_)) (mul_le_mul (hf.pays one_le_two) (xBin hq hh) (norm_nonneg _) hf.pos)).trans_eq ?_
        · rw [norm_mul]; exact mul_le_mul (xBin hf hh) (hq.pays one_le_two) (norm_nonneg _) (by unfold Duo; have h:=hf.pos; have he:=hh.pos; positivity)
        unfold trioK Duo; ring
lemma Left2 (hp:Cane μ p C)(hh:Cane μ p' D)(hq:Cane μ q A):κ2 μ (p-p') q=κ2 μ p q-κ2 μ p' q:=by
       unfold κ2 a_; rw [sub_mul (p) p', show (∫ x,(p*q-p'*q) x ∂μ)=_ from integral_sub (hp.mul hq).strong (hh.mul hq).strong,show (∫ x,(p-p') x ∂μ)=_ from integral_sub hp.strong hh.strong]; ring
lemma κ2_shift (hp:Cane μ p C)(hp':Cane μ p' C)(hq:Cane μ q D)(hq':Cane μ q' D)(hh:Cane μ (p-p') A)(hw:Cane μ (q-q') B) :
             ‖κ2 μ p q-κ2 μ p' q'‖≤ Duo (A 2) (D 2)+ Duo (B 2) (C 2):=by rw [show κ2 μ p q-_=κ2 μ (p-p') q+κ2 μ (q-q') p' from by rw [Left2 hp hp' hq,Left2 hq hq' hp',Swap2 μ q p',Swap2 μ q' p'];ring]; exact (norm_add_le ..).trans (add_le_add (xBin (hh _ two_pos) (hq _ two_pos)) (xBin (hw _ two_pos) (hp' _ two_pos)))
lemma Left3 (hp:Cane μ p C)(hh:Cane μ p' D)(hq:Cane μ q A)(hv:Cane μ r B): κ3 μ (p-p') q r= κ3 μ p q r-κ3 μ p' q r:=by
       rw[beak3,beak3,beak3,sub_mul (p) p',Left2 (hp.mul hq) (hh.mul hq) hv, Left2 hp hh hv,show a_ μ (p-p')= a_ μ p-a_ μ p' from integral_sub hp.strong hh.strong]; ring
variable {B' C':price}
lemma κ3_shift (hp:Cane μ p C)(hp':Cane μ p' C)(hq:Cane μ q D)(hq':Cane μ q' D)(hv:Cane μ r B')(hv':Cane μ r' B')(hh:Cane μ (p-p') A)(hw:Cane μ (q-q') B)(hg:Cane μ (r-r') F):
            ‖κ3 μ p q r-κ3 μ p' q' r'‖≤ trioK (A 4) (D 4) (B' 4) + trioK (B 4) (C 4) (B' 4)+trioK (F 4) (C 4) (D 4):=by
             rw[show κ3 μ p q r-_ = (κ3 μ (p-p') q r+κ3 μ (q-q') p' r)+κ3 μ (r-r') p' q' from by
                  rw [Left3 hp hp' hq hv,Left3 hq hq' hp' hv,Left3 hv hv' hp' hq',← (Order3 μ p' q r).2, ← (Order3 μ p' q' r).2, ← (Order3 μ p' r q').2, ← (Order3 μ p' q' r).1, ← (Order3 μ p' r' q').2,← (Order3 μ p' q' r').1]; ring]
             have he: (0:ℕ)<4:=by decide
             exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (xTern (hh 4 he) (hq 4 he) (hv 4 he)) (xTern (hw 4 he) (hp' 4 he) (hv 4 he)))) (xTern (hg 4 he) (hp' 4 he) (hq' 4 he)))
end
end YM.OPE.Borealis.Galea
