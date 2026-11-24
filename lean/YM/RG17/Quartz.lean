import YM.RG17.Mirror
/-!
# Height preservation of last punch with coupling toll of ANY fixed order
 Input toll sub-power ANY, thus no params strengthened. Height, όχι polylog step-count
 nor poly-L. Choose explicit last punch criterion (still on exact hatted clock).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Filter Set Lattice RG MeasureTheory Spec OPE OPE.Orbits
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)
set_option quotPrecheck false
local notation "T"=> OPE.run
local notation "s"=> C.S.scale
-- tau i chosen such that log C ≤ logloss/8. charge `a'` force in Gℓ calibrated. h home
lemma pole {m:ℝ→ℕ} (h:Height C.S home OPE.run m 1){q c:ℝ→ℝ} (he:RateIs home OPE.run q 0)(hv:RateIs home OPE.run c 0): ∃ l:ℝ→ℕ, Height C.S home OPE.run l 1 ∧ ∀ᶠ r in home, l r < m r ∧ q r / Bid.gainChart C.path (m r) (l r) < c r:=by
    let Y(r):=s (m r) - 8*(|Real.log (q r/c r)|+1)
    have hC:Tendsto (fun r=>Real.log (q r/c r)/T r) home (𝓝 0):=by simpa only [sub_zero] using! (he.div hv).rate
    have hμ : Tendsto (fun r=> |Real.log (q r/c r)|/ T r) home (𝓝 0):=by
       rw [← abs_zero (α:=ℝ)]; refine hC.abs.congr' ?_; filter_upwards [ageLarge.eventually_gt_atTop 0] with r hr; rw [abs_div,abs_of_pos hr]
    have ht:Tendsto (fun r=>Y r / T r) home (𝓝 1):=by
       have hx:= h.pace.sub ((hμ.add (tendsto_const_nhds (x:= (1:ℝ))|>.div_atTop ageLarge)).const_mul 8); rw [add_zero,mul_zero,sub_zero] at hx; exact hx.congr fun i=>by unfold Y; ring
    have hp:Tendsto Y home atTop:= ((ht.pos_mul_atTop (by norm_num) ageLarge)).congr' ((ageLarge.eventually_gt_atTop 0).mono fun i hi=> div_mul_cancel₀ _ hi.ne') -- order?
    have hh(i) := (C.S.divergent.eventually_gt_atTop (Y i)).exists; let l i:=Nat.find (hh i); have hl(i):Y i<s (l i):=Nat.find_spec (hh i)
    have hv':Tendsto l home atTop:= tendsto_atTop.mpr fun j=>by filter_upwards [hp.eventually_ge_atTop (s j)] with i hi using ((OPE.scale_mono C.S).le_iff_le.mp (le_trans hi (hl i).le))
    let X(i):= l i-1; have hX:Tendsto X home atTop:= tendsto_atTop.mpr fun j=> by filter_upwards [hv'.eventually_gt_atTop j] with i hi;unfold X;omega
    have hx(i):1 ≤ l i→ s (X i) ≤ Y i:= by
       intro hv; apply le_of_not_gt; intro ht; have hY: l i ≤ X i:= Nat.find_min' (hh i) ht; unfold X at hY; omega
    refine ⟨X,⟨hX,?_⟩,?_⟩
    · let a(r:ℝ):=s (X r); have hz:Tendsto a home atTop:= C.S.divergent.comp hX
      have hy:Tendsto (fun i=>s (l i)/a i) home (𝓝 1):=by
         have hh := (C.path.levels.fits.mesh); unfold Schedule.Gentle at hh
         refine (show Tendsto (fun i=> 1+ Real.log (C.S.block (X i)).val /a i) home (𝓝 1) from by simpa only [add_zero] using! ((hh.comp hX).const_add 1)).congr' ?_
         filter_upwards [hz.eventually_gt_atTop 0,hv'.eventually_ge_atTop 1] with i he hH; rw [← (show X i+1=l i from Nat.sub_add_cancel hH),C.S.scale_succ,add_div, (show s (X i) / a i=1 from div_self he.ne')]
      have hY:Tendsto (fun i=>Y i/a i) home (𝓝 1):=by
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hy ?_ ?_
          · filter_upwards [hv'.eventually_ge_atTop 1,hz.eventually_gt_atTop 0] with i hi he using (one_le_div he).mpr (hx i hi)
          filter_upwards [hz.eventually_ge_atTop 0] with i he using div_le_div_of_nonneg_right (hl i).le he
      have he:= ht.div hY (by norm_num); rw [div_one] at he; refine he.congr' ?_; filter_upwards [hp.eventually_gt_atTop 0] with i hi; change Y i /_/(Y i/a i)=a i/T i; rw [div_div_eq_mul_div,div_mul_eq_mul_div, mul_div_right_comm]; field_simp
    filter_upwards [hv'.eventually_ge_atTop 1,hv.pos,he.pos] with r hr hH hN
    have hp:=hx r hr; unfold Y at hp; let u:= q r / c r; let Z:=Bid.gainChart C.path (m r) (X r); constructor
    · refine (OPE.scale_mono C.S|>.lt_iff_lt.mp ?_); have he:0 ≤ |Real.log (q r/c r)|:=abs_nonneg _; linarith only [he,hp]
    apply (div_lt_iff₀ (show 0 < Z from Real.exp_pos _)).mpr; rw [mul_comm]
    apply (div_lt_iff₀ hH).mp; apply (Real.log_lt_iff_lt_exp (div_pos hN hH)).mp; linarith only [hp,le_abs_self (Real.log (q r/c r))]
-- may actually log_div etc
end YM.RG17
