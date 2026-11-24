import YM.OPE.Compatible.Cum.Gray
/-!
# Cost agenda. before μ etc. State abstraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J E:Type}{N:Side} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E} [Fintype I]
local notation "Q!"=> deck I N
local notation "K!"=> Flume.Script.Tab I N
variable [DecidableEq J]{s:Finset J}{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{X:J→Option (Site N)} {ρ:J→Bool} {a b:Site N}{c y κ σ l:ℝ}{Z:E→L[ℝ] deck I N}{Ω:Row I I}{C:ℕ→ℝ}{p e k d t n m h:ℕ}{F H:Curtain I}{r:J→ℝ}{x:deck I N}
section
omit [Fintype I]
lemma moldTrip {a b c u v:ℝ}(h:Mold a b u N m)(hf:Mold b c v N m): Mold a c (u+v) N m:= (mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub a b c) (show 0≤ grain N m from zero_le_one.trans (grain_b _))).trans (by rw [mul_add]; exact add_le_add h hf)
lemma moldAdd {a b c d u v:ℝ}(h:Mold a b u N m)(hf:Mold c d v N m): Mold (a+c) (b+d) (u+v) N m:=by unfold Mold; rw [add_sub_add_comm]; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (show 0≤grain N m from zero_le_one.trans (grain_b _))).trans (by rw [mul_add];exact add_le_add h hf)
lemma moldSum {A V p:J→ℝ}(h:∀ i∈s, Mold (A i) (V i) (p i) N m): Mold (∑ i∈s,A i) (∑ i∈s,V i) (∑ i∈s,p i) N m:=by induction s using Finset.induction_on with | empty=>simp [Mold] | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,sum_insert hi]; exact moldAdd (h _ (mem_insert_self ..)) (ih (fun j hj=> h _ (mem_insert_of_mem hj)))
lemma moldZero (a:ℝ)(hy:0≤y): Mold a a y N m:=by simpa [Mold]
end
lemma RollLeft (x: Q!)(b:ℝ)(hb:0≤b)(ht:d≤e): b*(1+‖x‖)^d ≤ b*(1+‖x‖)^e:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) ht) hb
def Texter (v w:J→ℕ)(s:Finset J)(κ σ:ℝ)(m n d e:ℕ)(C:ℕ→ℝ)(I: Type)[Fintype I] : Prop:= ∃ D:ℝ,0 ≤ D ∧ ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I),Ω.strip σ κ →∀ (N:Side)(Q:∀ i,Script I (w i+v i))(Z:E→L[ℝ] deck I N)(a:Site N)(X:J→Option (Site N))(c:ℝ)(x:deck I N),Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c→∀ r:J→ℝ, coversB v w Q m r s→∀ R:Script I (e+d),∀ b:ℝ,soot m R b→∀ j,Rollup v w s d e ≤ j→ Scripture (e:=e) (d:=d) v w Ω Q R μ L x Z X a c s j n (D*b*Visit r s)
-- tap small
lemma payJ {f:E→ℝ}(h:Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c)(he:coversB v w Q m r s)(hp:BeamS (grain N m • f) y (clockY x Z) p)(hx:0≤y)(hk: k+HueS s≤m):
    grain N k * ‖Tap μ L (Fig v w Q X c x Z) f s‖ ≤ Aroma J I (w+v) (C 0) p s * (1+‖x‖)^(p+Mani (w+v) s)* y*Visit r s:=by
       let g:= Tap μ L (Fig v w Q X c x Z) f s; have hh:= Brick (μ:=μ) h.fee.alive hp hx (plotme x s r h.amp he (X:=X)); rw [Tap_scale,norm_mul,Real.norm_of_nonneg (show 0≤grain N m from zero_le_one.trans (grain_b _))] at hh; apply le_of_mul_le_mul_left (a:=grain N (HueS s)) _ (zero_lt_one.trans_le (grain_b (N:=N) _)) -- arguments
       rw [← mul_assoc,← grainPlus]; apply le_trans _ (le_trans hh _) -- type unknown
       · apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); unfold grain; gcongr; exact_mod_cast N.pos; omega
       apply le_of_eq; ring
lemma payCut {u v':E→ℝ}(hp:Bond u)(ht:Bond v')(h:Buds Ω L x C Z (w:=w) (v:=v) Q a s X m c)(he:coversB v w Q m r s)(hw: BeamS (grain N m • (u-v')) y (clockY x Z) p)(hx:0≤y)(hk:k+HueS s≤ m): Mold (Tap μ L (Fig v w Q X c x Z) u s) (Tap μ L (Fig v w Q X c x Z) v' s) (Aroma J I (w+v) (C 0) p s * (1+‖x‖)^(p+Mani (w+v) s) * y *Visit r s) N k:=by
      let t:=Fig v w Q X c x Z; have hv : okP t s:= branches v w _ x x Z s -- wrong
      have he' : Tap μ L t (u-v') s= Tap μ L t u s-Tap μ L t v' s:=eq_sub_of_add_eq ((Tap_merge μ L t s hv _ v' (hp.sub ht) ht).symm.trans (by rw [sub_add_cancel]))
      change grain N k * ‖Tap μ L t u s-Tap μ L t v' s‖ ≤ _; rw [←he']; exact payJ h he hw hx hk
end YM.OPE.Libra.Shell
