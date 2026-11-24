import YM.OPE.Compatible.Lark.Eon
/-!
# Second seam quantitative
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J:Type}{n c f:Side} {s d U D:ℝ}{i r k:ℕ}
open Page Planned.PrimaryIntegral295.Carrier
variable [Fintype I][Fintype J]
lemma padCash (A:Row I I)(H:A.strip s U)(h:0<s)(hx:0≤U)(k:ℕ)(p:Script I (r+2))(hp: soot (4+k) p d)(w:Fin r→deck I n):
     (n.val:ℝ)^k * ‖cityTap (A.acts n) p w-library n (pad A p) w‖ ≤(8:ℝ)^(4+k)*widthCost s (4+k)*U*d *(∏ j,‖w j‖):=by
       let v:ℝ:=(8:ℝ)^(4+k)*widthCost s (4+k)*U*d; let l:ℝ:= n.val; have hl:0<l:=Nat.cast_pos.mpr n.pos; have he(a:Site n): l^k*‖routeTap (A.acts n) p w a-scribe a (pad A p) w‖≤ (v*(∏ j,‖w j‖))/(l^4):=by
          rw [le_div_iff₀ (pow_pos hl 4), show l^k * _*l^4=l^(4+k)*‖routeTap (A.acts n) p w a-scribe a (pad A p) w‖ by ring]; refine (pad_layers A H h hx p d hp n w a).trans_eq ?_; unfold v; ring
       rw [cellarT,library,← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hl.le k)).trans; rw [mul_sum]; apply (sum_le_sum (fun a _=>he a)).trans_eq; rw [sum_const,card_univ,Lattice.site_card,nsmul_eq_mul]; push_cast; exact mul_div_cancel₀ _ (pow_pos hl 4).ne'
omit [Fintype I][Fintype J] in
lemma plusRoots (A:Row J J)(h:A.strip s D)(ht:0≤D): (ROOT (I:=I) A).strip s D:=by
      intro a b; rcases a with a|a<;>rcases b with b|b <;> first | exact h _ _ | (simp [ROOT,toLeft,Width,RG.SumBudget,ht])
lemma TuneHi (T:Row J J)(k:ℕ)(hs:0<s)(ht:T.strip s d)(hp:0≤d)(A:Script (I⊕J) 3)(p:Script (I⊕J) 4)(h:soot (4+k) p U)(V:ℝ)(hx:soot (4+k) (cotton (ROOT T) A A) V)(x: Fin 2→deck (I⊕J) c):
     ((c.val:ℝ)^k) * ‖tuneH T A p c x-library c (tuneV T A p) x‖≤8^(4+k) * widthCost s (4+k)*d*(2*V+U)*(∏ i,‖x i‖):=by
        let τ:=(ROOT (I:=I) T); let H:= cotton τ A A; let u:= swing (Equiv.swap (1:Fin 4) 2) H; let W:= τ.acts c; let L:ℝ:= (c.val:ℝ)^k; have hh : τ.strip s d:= plusRoots _ ht hp; have hv: soot (4+k) u V:= swing_fee hx _; let Q(i:Script (I⊕J) 4):= cityTap W i x-library c (pad τ i) x; let C':= (∏ i,‖x i‖); have hc0: 0≤ C':=prod_nonneg fun i _=> norm_nonneg _; let D':ℝ:=8^(4+k) * widthCost s (4+k)*d
        have hp0(i: Script (I⊕J) 4)(D:ℝ)(hi:soot (4+k) i D):L*‖Q i‖≤ D'*D*C':=padCash τ hh hs hp k i hi _
        have he := hp0 H _ hx; have hu:= hp0 u _ hv; have hP:= hp0 p _ h
        have hi : L*‖Q p-Q H-Q u‖≤ D'*(2*V+U)*C':=by
             have hl:0≤L:=pow_nonneg (Nat.cast_nonneg _) _; apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add_left (norm_sub_le ..) _)) hl).trans; nlinarith only [he,hu,hP]
        have hS : Summable (pad τ H):= sootS (pad_charge hh hs.le hp hx); have hR:= sootS (pad_charge hh hs.le hp h); let V₀:= Q p-Q H-Q u
        rw [show tuneH T A p c x-library c (tuneV T A p) x= V₀/2 from ?_]; apply le_trans (b:=L * ‖V₀‖) _ hi
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _); rw [norm_div]; norm_num
        change (1/2)*(-cityTap W H x+cityTap W p x-cityTap W u x)-library c ((1/2:ℝ) • (((-1:ℝ) • pad τ H + pad τ p)+ (-1:ℝ) • pad τ u)) x=_
        have hf:=sootS (Sack.scale_line (pad_charge hh hs.le hp hx) (-1:ℝ));rw [libScale,libAdd ((-1:ℝ) • pad τ H+pad τ p) _ (hf.add hR) (sootS (Sack.scale_line (pad_charge hh hs.le hp hv) _)),libAdd _ _ hf hR, libScale,libScale]; unfold V₀ Q;ring
end YM.OPE.Flume.Script
