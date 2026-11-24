import YM.Frontier6.Bouquet.Truth.Conduct
/-!
# From logarithmic ratios to honest uniform small-loss estimates

Use along trajectories where **all** ratios converge so can ask programs on
 logarithmic ties and strictly across bands. Floor retains additional unobserved
 valuations if needed (transaction asked along trees of arbitrary finite depth).
 Price normalization may consume any unspecified allowance here; instantiate from
 known powers in those actual contexts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Filter Set Finset Spec Road Forest Tale Fareway Real
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I L J:Type}
structure Ribbon (I L:Type) where
   floor: I → ℝ
   length: I→ L→ ℝ
   covered : ∀ i l,floor i ≤ length i l ∧ length i l ≤ 1
   ground : ∀ i,0<floor i ∧ floor i≤ 1
namespace Ribbon
variable (R: Audit.Ribbon I L)
abbrev ruin (i:I)(ε:ℝ):= R.floor i ^ (-ε)
lemma footing (i:I): 0<R.floor i:= (R.ground i).1
lemma leg_pos (i:I)(x:L): 0<R.length i x:= lt_of_lt_of_le (R.footing i) (R.covered ..|>.1)
def pull (g:J→ I):Ribbon J L:= ⟨R.floor ∘ g,R.length ∘ g,fun i l=> R.covered _ _,fun i=> R.ground _⟩
-- exploration
variable (T: Fareway J)(f:J→ I)
def Speaks (c:L→ℝ):Prop:=∀ i:L, T.Mint (fun j=>R.length (f j) i) (-(c i))
lemma speaks_nonneg [T.via.NeBot] {x:L→ℝ} (he:R.Speaks T f x) (i:L): 0 ≤ x i:=by
   by_contra hc; obtain ⟨j,hj⟩:= ((T.minted_c 1 one_pos).cheaper (he i) (by linarith)).exists; exact hj.not_ge (R.covered _ i).2
lemma told {X:Type*} [SeminormedAddCommGroup X] (F:I→ X)(h:∀ (J:Type)(g:J→ I)(T:Fareway J) [T.via.NeBot], ∀ x:L→ℝ, R.Speaks T g x → T.Costs (F ∘ g) 0) (ε:ℝ)(hε:0<ε): ∃ C:ℝ,0 ≤ C ∧∀ i, ‖F i‖≤ C* R.ruin i ε:=by
   by_contra hf
   let C n:= Real.exp ((n:ℝ)*ε)
   have H(n:ℕ): ∃ i:I,C (n:ℝ)*R.ruin i ε < ‖F i‖:= by specialize hf; by_contra hh; push Not at hh; exact hf ⟨C (n:ℝ), (Real.exp_pos _).le,hh⟩
   choose z hZ using H; let r i:= R.floor (z i); let c (i:ℕ):= (i:ℝ) - Real.log (r i); have hx:Tendsto c atTop atTop:=tendsto_atTop_mono' atTop (Eventually.of_forall fun (i:ℕ)=>(show (i:ℝ)≤ c i from by unfold c r; linarith only [Real.log_nonpos (R.footing (z i)|>.le) (R.ground (z i)|>.2)])) tendsto_natCast_atTop_atTop
   let V: Ultrafilter ℕ:= Ultrafilter.of atTop; have hv:= Ultrafilter.of_le (atTop:Filter ℕ); let T: Fareway ℕ:=⟨V.toFilter,c,hx.mono_left hv⟩; have hh (x:L):∃ a:ℝ,T.Mint (fun i=> R.length (z i) x) (-a):=by
       let f i:= R.length (z i) x; let g i:=Real.log (f i)/c i; have hg:∀ᶠ i in V.toFilter,g i∈ Icc (-1:ℝ) 0:=by
           filter_upwards [show ∀ᶠ i in V.toFilter,0<c i from T.ahead] with i hi; have he:= R.ground (z i); have hu:= R.covered (z i) x; have hz:r i ≤ f i:= hu.1; refine ⟨(le_div_iff₀ hi).2 (le_trans ?_ (Real.log_le_log he.1 hz)), div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (R.leg_pos _ _|>.le) hu.2) hi.le⟩; unfold c r; linarith only [Nat.cast_nonneg (α:=ℝ) i]
       obtain ⟨b,hb,hC⟩:= isCompact_Icc.ultrafilter_le_nhds' (V.map g) (by rw [Ultrafilter.mem_map]; exact hg); exact ⟨-b,Eventually.of_forall fun i=> R.leg_pos _ _,(by rw [neg_neg]; exact hC)⟩
   choose x hX using hh; letI : T.via.NeBot:= V.neBot; obtain ⟨i,hi⟩:= (h ℕ z T x hX _ hε).exists; have he:=hZ i;
   have hq:R.ruin (z i) ε=Real.exp (-(Real.log (r i)*ε)):=by unfold ruin r; rw [Real.rpow_def_of_pos (R.footing _),mul_neg]; -- align
   rw [hq] at he; unfold C at he; rw [← Real.exp_add] at he; change ‖F (z i)‖ ≤ Real.exp (((i:ℝ)-Real.log (r i))*ε) at hi; rw [← sub_eq_add_neg, ← sub_mul] at he; exact he.not_ge hi
end Ribbon
end YM.Frontier6.Bouquet.Audit
