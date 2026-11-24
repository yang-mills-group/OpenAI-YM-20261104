import YM.OPE.Compatible.Cum.Buck
/-!
# One bill for folded Gaussian moments. purely polynomial in side. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier
variable {I J E R:Type}{A:Row I I}{N:Side}{n:ℕ} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E) [Fintype I]
local notation "Q!"=>deck I N
local notation "TK"=> Flume.Script.Tab I N
def BeamS (p:E→ℝ)(x:ℝ)(a:E→ℝ)(b:ℕ):Prop:= Bond p∧∀ i:E,‖p i‖ ≤ x * (a i)^b
section
variable {D:ℝ}
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E][Fintype I] in lemma BeamS.mon {u:ℕ}{x:E→ℝ}{y:E→ℝ}(b:BeamS x D y n)(hd:0≤D)(he:1≤y)(hp:n≤u) :BeamS x D y u:=⟨b.1,fun i=>(b.2 i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (he i) hp) hd)⟩
end
lemma monetary (u:E→ℝ)(v:E→ℝ)(_h:Bond u)(hp:Bond v)(hv:∀ i, ‖u i‖≤v i): ‖L.average μ u‖ ≤ L.average μ v:=by
    unfold Law.average; rw [norm_div]; have hp' : 0≤∫ x:E,L.kern x ∂μ:=integral_nonneg fun i=> Real.exp_nonneg _; rw [Real.norm_of_nonneg hp']; apply div_le_div_of_nonneg_right _ hp'; apply norm_integral_le_of_norm_le (lumpZ μ L v hp); refine Eventually.of_forall ?_; intro i; rw [Pi.mul_apply,norm_mul, show ‖L.kern i‖= L.kern i from Real.norm_of_nonneg (Real.exp_nonneg _)]; exact mul_le_mul_of_nonneg_right (hv i) (Real.exp_nonneg _)
-- recurrence moment from centered. Γ translation Lemma
lemma riseMoment (φ:Dual' E)(v:ℕ):
    L.average μ (⇑φ^(v+2))= ((v+1:ℕ):ℝ)*L.wick φ φ *L.average μ (⇑φ^v):=by
         let c:=(v+1:ℕ); let A:E→ℝ:=φ; let b:=(c:ℝ)*L.wick φ φ; let q:=L.inverse φ; have hp:(A)^(v+2)=L.P q * (A^c):=by rw [L.applies]; exact pow_succ' A (v+1)
         rw [hp,bask μ L q _ (b • (A^v)) ( (Bond.glyph φ).pow _) (Bond.scale b ((Bond.glyph φ).pow _)),scooted]; intro i t; let P:= i+t • q; simp only [Pi.pow_apply,Pi.smul_apply]; change HasDerivAt (fun u:ℝ=> (φ (i+u • q))^c) (b*(φ P)^v) t; have hh:HasDerivAt (fun x:ℝ=>φ (i+x • q)) (L.wick φ φ) t:=by simp only [map_add,map_smul,smul_eq_mul]; simpa only [one_mul] using! (((hasDerivAt_id' t).mul_const (φ q)).const_add ..)
         convert! hh.pow c using 1; unfold b c; simp only [Nat.add_sub_cancel];ring -- expand P
lemma mediate (φ:Dual' E)(a:ℕ)(b:ℝ)(h: ‖L.wick φ φ‖ ≤ b): ‖L.average μ (⇑φ^(2*a))‖ ≤ ( (2*a).factorial:ℝ)*b^a:=by
         have hb:0 ≤ b:=(norm_nonneg _).trans h
         induction a with
         | zero=>simp [L.empty]
         | succ a ih=> rw [show 2*(a+1)= 2*a+2 from by omega,riseMoment,norm_mul,norm_mul,norm_natCast]; let k:= 2*a; apply (mul_le_mul (mul_le_mul_of_nonneg_left h (by positivity)) ih (norm_nonneg _) (by positivity)).trans; rw [Nat.factorial_succ,Nat.factorial_succ (2*a)]; push_cast; rw [pow_succ]; calc
                        _=(2*(a:ℝ)+1)* (( (2*a).factorial:ℝ)* b^a*b):=by ring
                        _ ≤ ((2*a+1+1) * ( (2*(a:ℝ)+1))) *(( (2*a).factorial:ℝ)* b^a*b):= by gcongr; nlinarith
                        _= _:=by ring
-- bundle max powers
variable {C:ℝ} (Z:E→L[ℝ] deck I N)(z:deck I N)
def clockY (p:Q!)(Z:E→L[ℝ] deck I N)(i:E):ℝ:=1+‖p‖+‖Z i‖
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma tallY : (1:E→ℝ)≤ clockY z Z:= by intro i;change 1≤1+_+_; linarith only [norm_nonneg z, norm_nonneg (Z i)]
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma scale_gate (z:E)(d:ℕ): ‖Z z‖ ^ d ≤ 1+ ∑ i:TK,Ferry Z i z ^ (2*d) := by
    let v:=Z z; have he(i:TK):0≤ Ferry Z i z ^(2*d):= by rw [Nat.mul_comm,pow_mul]; positivity
    by_cases h:‖v‖ ≤ 1; · exact (pow_le_one₀ (norm_nonneg _) h |>.trans (le_add_of_nonneg_right (sum_nonneg fun i _=>he _)))
    have hp: 1 < ‖v‖:= lt_of_not_ge h; obtain ⟨i,hi⟩:∃ i: TK,‖v i‖=‖v‖:=by
         have ha : Nonempty TK:= by by_contra! hx; exact (hp.not_ge) ( (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=> (IsEmpty.false i).elim))
         by_contra! hy; exact lt_irrefl ‖v‖ ((pi_norm_lt_iff (zero_lt_one.trans hp)).mpr fun i=> lt_of_le_of_ne (norm_le_pi_norm ..) (hy i))
    suffices heQ: ‖v‖^d ≤ Ferry Z i z^(2*d) from heQ.trans ((single_le_sum (f:=fun i:TK=> Ferry Z i z^(2*d)) (fun i _=> he _) (mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))
    apply le_trans (pow_le_pow_right₀ hp.le (show d≤ 2*d by omega)); change _ ≤ v i^(2*d); rw [← hi, ← Real.norm_of_nonneg (show 0≤ v i^(2*d) from he i)]; rw [norm_pow] -- need `Real.`
end YM.OPE.Libra.Shell
