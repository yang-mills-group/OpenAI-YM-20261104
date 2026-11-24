import YM.OPE.Compatible.Cum.Music
/-!
# aspiration polynomial oomph. coefficient against flow of any clocks
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier
variable {I J E:Type}{N:Side} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E) [Fintype I]
local notation "TK"=> Flume.Script.Tab I N
local notation "Q!"=> deck I N
section pow
variable {u y:ℝ}
lemma sumPower (k:ℕ)(hp:0≤u)(hx:0 ≤ y):(u+y)^k ≤ (2:ℝ)^k*(u^k+y^k):=by
      rcases le_total u y with he|he
      · calc
           _≤(2*y)^k:=pow_le_pow_left₀ (add_nonneg hp hx) (by linarith) _
           _=2^k*y^k:=mul_pow ..
           _≤ _:=by gcongr;exact le_add_of_nonneg_left (pow_nonneg hp _)
      calc
        _≤(2*u)^k:=pow_le_pow_left₀ (add_nonneg hp hx) (by linarith) _
        _= _ :=mul_pow ..
        _≤ _:=by gcongr; exact le_add_of_nonneg_right (pow_nonneg hx _)
end pow
-- power self legs
abbrev quotaB (I:Type)[Fintype I](b:ℝ)(k:ℕ):ℝ:=2^k*(2+(Fintype.card I) * ((2*k).factorial:ℝ)*b^k)
variable (Z:E→L[ℝ] deck I N){a:ℝ}
def Sustains (a:ℝ): Prop:=0 ≤ a ∧ ∀ i:TK, ‖Oriel L Z i i‖≤ a
lemma Mile (h:Sustains L Z a)(x:Q!)(u:E→ℝ)(b:ℝ)(hb:0 ≤ b)(k:ℕ)(hv:BeamS u b (clockY x Z) k):
      ‖L.average μ u‖ ≤ (N.val:ℝ)^4*quotaB I a k*(1+‖x‖)^k*b:=by
        let T:=(N.val:ℝ); have hT: 1 ≤ T:=by unfold T; exact_mod_cast (show (1:ℕ)≤N.val from N.pos)
        let V:= Ferry Z; let r:=1+‖x‖; have hr : 1 ≤ r := le_add_of_nonneg_right (norm_nonneg _); let X (i:TK):= ⇑(V i)^(2*k); let q:E→ℝ:= (fun _=> r^k+1)+∑ i:TK,X i; have hx(i:TK) : Bond (X i):=(Bond.glyph _).pow _; have hQ:Bond q:= (Bond.keep _).add (Sumbond _ _ fun i _=>hx i)
        have he(i:E) : (clockY x Z i)^k ≤ (2:ℝ)^k * q i:=by
             refine (sumPower k (zero_le_one.trans hr) (norm_nonneg (Z i))).trans ?_; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold q; simp only [Pi.add_apply,Finset.sum_apply]; rw [add_assoc]; exact add_le_add_right (scale_gate Z i k) _
        let c:= b * (2:ℝ)^k; have hc:0 ≤ c:= mul_nonneg hb (by positivity)
        apply (monetary μ L u (c • q) hv.1 (Bond.scale c hQ) (fun i=> (hv.2 i).trans (by rw [Pi.smul_apply, smul_eq_mul,mul_assoc (show ℝ from b)]; exact mul_le_mul_of_nonneg_left (he i) hb))).trans; rw [scooted]; unfold q; rw [sun _ _ (Bond.keep _) (show Bond (∑ i:TK,X i) from Sumbond _ _ fun i _=>hx i), singleConst,science μ L _ X fun i _=>hx i]; let p:ℝ:=((2*k).factorial:ℝ)*a^k; let N':ℝ:= Fintype.card I; have ha:=h.1
        have ht: (∑ i:TK,L.average μ (X i))≤ T^4*N'*p:=by
             apply (sum_le_sum (f:=fun i=> L.average μ (X i)) (g:=fun i=> p) (fun i _=> (le_abs_self _).trans (mediate μ L (V i) k a (h.2 i)))).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_prod,site_card]; unfold T N';push_cast;rfl -- req
        change _ ≤ T^4*(2^k*(2+ N'* ( (2*k).factorial:ℝ) * a^k))*r^k*b
        have hb: 0 ≤ p:=mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha _); have hW:1≤r^k:=one_le_pow₀ hr; have hk:1≤ T^4:=one_le_pow₀ hT; have hz:0 ≤ N':=Nat.cast_nonneg _
        apply (mul_le_mul_of_nonneg_left (add_le_add_right ht (r^k+1)) hc).trans
        calc
          c*(r^k+1+T^4*N'*p)≤ c*(r^k*T^4+r^k*T^4+(T^4*N'*p)*r^k):=mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_mul_of_one_le_right (by positivity) hk) (one_le_mul_of_one_le_of_one_le hW hk)) (le_mul_of_one_le_right (by positivity) hW)) hc
          _ =_:=by unfold c p; ring
end YM.OPE.Libra.Shell
