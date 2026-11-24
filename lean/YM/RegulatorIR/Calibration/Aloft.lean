import YM.RegulatorIR.Stage.Illumination

/-!
# Affine increments on Rank 2 transport

We cannot assume T converges in order to estimate/construct the clocks
needed by T. Use *one coefficient* valuation transport; applies at any
prior readings. Time steps free of composition radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X Y U V Z: Type} {e r p m:ℕ}
section Abstract
variable {T K:Packet X r} {T' V':Orders X} {b : Packet X 2} (B:Layer X X)
lemma add_l (h: Limits K)(H:Limits T): Limits (K+T):= by
 obtain ⟨a,ha,hA⟩:=h; obtain ⟨b,hb,Hb⟩:=H; refine ⟨a+b,by finiteness,fun x=>(enorm_add_le ..).trans (add_le_add (hA x) (Hb x))⟩
lemma tilt_l (h:Limits K)(v:ℝ): Limits (v • K):=by obtain ⟨a,h,H⟩:=h; exact ⟨‖v‖ₑ*a,by finiteness,fun x=> by change ‖v*K x‖ₑ ≤ _;rw [enorm_mul]; apply mul_le_mul_right (H _ )⟩
lemma fanned (h : Billed B)(hp: Limits K)(hh: Limits T): draft B (K+T)= draft B K+draft B T := by
 let l:=List.finRange r
 have hf : Packet.drawing (K+T) B l= Packet.drawing K B l+Packet.drawing T B l:=by
    ext1 x; rw [Pi.add_apply, wind_up (add_l hp hh) _ h _ l (List.nodup_finRange _),wind_up hp _ h _ l (List.nodup_finRange _),wind_up hh _ h _ l (List.nodup_finRange _),← (pricedField hp _ h x l).tsum_add (pricedField hh _ h x l)]
    apply tsum_congr; intro v; unfold Gradient.field;split; exact add_mul ..;simp
 unfold Packet.draft;rw [hf,symmetry_sum']
variable {P:ℝ}{A₀:Deck P X U}{A₁:Deck P Y V}
variable (D: GridStep A₀ A₁)
lemma pull_a {W T:Packet (X⊕Y) r}(h:Billed D.driftL)(hp:Limits T)(hh:Limits W): D.pullI (T+W)=D.pullI T+D.pullI W:=by unfold GridStep.pullI;rw [fanned _ h hp hh];rfl
lemma pull_m (W:Packet (X⊕Y) r)(c:ℝ) : D.pullI (c • W)= c • D.pullI W:=by unfold GridStep.pullI; rw [Sources.scaleDraft];rfl
-- prior Clock. heat.
lemma statics (h:Vacuum T') : logHeat B T' false e 0=0:=funext fun r=> Classical.byContradiction fun hv=> Nat.lt_irrefl _ (heated_cap B T' h false 0 r e hv).1
lemma force_z (W:Ranked X) : force B 0 W=0 ∧ force B W 0=0:=by
 constructor <;> ext1 r <;> by_contra! h <;> obtain ⟨⟨i,j⟩,_,he⟩:= exists_ne_zero_of_sum_ne_zero (show _ ≠ (0:Packet X r) from h)
 exact (match_comes he).2.1 rfl
 exact (match_comes he).2.2 rfl
lemma current (h: Vacuum T')(hp:Vacuum V')(H: Matches e T' V') (i r) : drift B (logHeat B T' false) (logHeat B T' false) i (e+1) r= drift B (logHeat B V' false) (logHeat B V' false) i (e+1) r:=by
 unfold Diagram.drift;apply sum_congr rfl;intro j _; unfold Diagram.carry; apply sum_congr rfl;intro ⟨b,c⟩ hv; simp only [mem_antidiagonal] at hv ⊢ -- bad
 by_cases ht:c=0
 · rw [ht,statics B h, statics B hp,(force_z ..).2,(force_z ..).2]
 by_cases hx:b=0
 · rw [hx,statics B h, statics B hp,(force_z ..).1,(force_z ..).1]
 rw [heat_m false H j.1 b (by omega),heat_m false H j.2 c (by omega)]
-- same e contribution ancestor extra ≥rank+2
lemma heights (h: Vacuum T')(hp: Vacuum V')(hv:Matches e T' V')(hf:T' (e+1)=V' (e+1)+peak b) (i) : logHeat B T' false (i+1) (e+1)= logHeat B V' false (i+1) (e+1):=by
 induction i with
 | zero=>
    ext1 r; rw [logHeat_next,logHeat_next]; split;rfl
    rename_i ht; rw [current _ h hp hv]; unfold heating;rw [logHeat_first,logHeat_first, if_neg (show ¬(r+2=0 ∧ false=false) by omega),if_neg (show ¬(r+2=0 ∧ false=false) by omega),hf,Pi.add_apply,peak_dark,add_zero]; exact fun he=> ht ⟨by omega,rfl⟩
 | succ i ih=>ext1 r; rw [logHeat_next,logHeat_next, current B h hp hv, ih]
lemma finale (h:Vacuum T')(hp: Vacuum V')(hv:Matches e T' V')(hf:T' (e+1)= V' (e+1)+peak b) : ceaseHeat B T' false (e+1)=ceaseHeat B V' false (e+1)+peak b:=by
 ext1 r; unfold ceaseHeat; rw [Pi.add_apply]; unfold heated; rw [sum_range_succ',sum_range_succ']; simp_rw [heights B h hp hv hf,logHeat_first]; split
 next hh=>rw [peak_dark b (by omega), add_zero,add_zero]
 next hh=>rw [hf,Pi.add_apply,add_assoc]
end Abstract
end YM.RegulatorIR.Calibration
