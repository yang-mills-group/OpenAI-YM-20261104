import YM.QuadraticLocal.Aperture.Dime
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Sage
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
open Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC PositionX.Gauss
open AllOrder.Catch AllOrder.Catch.Clock ConnectedActivityE6 Blaze Brush PositionX.Jet
variable {X Y Z ι:Type*} {V:Type}[Fintype V][DecidableEq V] {b a c:ι→ℝ} {k j:ℕ}
variable {T:AllOrder.Catch.Clock ι}
variable {γ:ℝ}
def lift (n:ℕ)(h:0<n)(T:AllOrder.Catch.Clock ι) : Catch.Clock ι:= ⟨T.rail,fun i=> T.cost i^n, (tendsto_pow_atTop h.ne').comp T.drive⟩
lemma meter {a:ℝ}(n:ℕ)(h:0<n)(T:Catch.Clock ι) : (Sage.lift n h T).Meter b a ↔ T.Meter b (a*n):= by
 have he: ∀ᶠ i in T.rail,1≤T.cost i:= T.pos; have hv : 0< (n:ℝ):= mod_cast h; let N:= (n:ℝ); let T':= Sage.lift n h T; have hh i (hi:1≤ T.cost i) (a:ℝ) : T'.cost i ^ a = T.cost i^(a*n) := by rw [mul_comm a,Real.rpow_mul (zero_le_one.trans hi),Real.rpow_natCast]; rfl
 constructor <;> intro u p hp
 · have hz:a<p/N:=(lt_div_iff₀ hv).mpr hp
   filter_upwards [u (p/N) hz,he] with i hi hk; refine hi.trans_eq ?_; rw [hh i hk, div_mul_cancel₀ p hv.ne'] -- isolated metavariable let N
 filter_upwards [u (p*n) (mul_lt_mul_of_pos_right hp hv),he] with i hi hx; exact hi.trans_eq (hh i hx p).symm
lemma lift_step (n:ℕ)(h:0<n)(hb:T.Meter b (-(1/2:ℝ))) : let a' i:=b i ^n; (Sage.lift n h T).Meter a' (-(1/2:ℝ)) := (meter ..).2 (hb.pow n)
lemma lift_s (n:ℕ)(h:0<n): (Sage.lift n h T).Meter b 0↔ T.Meter b 0:= (meter n h T).trans (by simp)

-- many prefixes.Y checks all measures & energies BEFORE.Offset depends patch costs. Horizon title. use for real log coefficient under current weight, tests independent; true Peer.Actor not bound-volume.M.
section
variable {X:ι→Type}[∀ i, MeasurableSpace (X i)] (W:∀ i,X i→ℝ)(μ:∀ i,Measure (X i))[∀ i,IsFiniteMeasure (μ i)] (ρ:∀ i,V→ X i→ℝ)
local notation "H"=> Fintype.card V
variable (he:∀ᶠ i in T.rail, Envelope (W i)∧0 ≤ (W i) ∧ (0< ∫ y,W i y ∂(μ i)) ∧ ∀ j:V,Envelope (ρ i j)) (v:ι→(V→ℝ)) (b:ι→ℝ)(hb:T.Meter b (-(1/2:ℝ)))(hx:∀ᶠ i in T.rail, 0<b i)
variable (hh:∀ᶠ i in T.rail, ∀ y:X i, W i y ≠0 → |member (ρ i) (v i,y)| ≤ a i)(ha:T.Meter a 0)
local notation "Q" => fun i j=> ratioN (W i) (μ i) (ρ i) j (v i)
local notation "N"=> fun i=> nap (W i) (μ i) (ρ i) (v i) (b i)
include he hb hx hh ha
lemma shot (j:ℕ): TaylorCap T j b N Q:= by
 let f i:= |a i|+1; have hp:T.Meter f 0:=ha.ab.add (Meter.const T 1); have hy:= (hb.mul hp).low (by norm_num) zero_lt_one
 have hf i:0<f i:=(by unfold f; positivity); constructor
 · intro k _; apply Meter.smaller (hp.pow k|>.weak (by simp)); filter_upwards [he,hh] with i hH hX; apply (Sage.sunny_guess (W i) (μ i) (ρ i) hH.1 hH.2.1 hH.2.2.1 (v i) (f i) k _ (hf i).le).trans (le_abs_self _); exact (fun y h=> (hX y h).trans (le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one))) -- improvise
 intro k hk; obtain ⟨C,hC,hZ⟩:= actual_T k; apply ((hb.mul hp|>.pow (k+1)).lscale C).weak (by unfold graded; simp) |>.smaller; filter_upwards [he, hh, hy, hx] with i hH hX hY h;
 refine (Sage.evening (W i) (μ i) (ρ i) hH.1 hH.2.1 hH.2.2.1 hH.2.2.2 (v i) (b i) (f i) C k (fun y hh=> ?_) h (hf i) ((le_abs_self _).trans hY.le) hZ).trans (le_abs_self _); exact (hX y hh).trans (le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one))
lemma fleer (j:ℕ): (∀ᶠ i in T.rail,0<N i) ∧ TaylorCap T j b (Real.log ∘ N) (fun i=> logS (Q i)) := by
 let h:= Sage.shot W μ ρ he v b hb hx hh ha j; have hz:Tendsto (fun i=>Q i 0) T.rail (𝓝 (1:ℝ)):= by
    refine tendsto_const_nhds.congr' (he.mono fun i hi=>?_ ); exact (show _ from congr_fun (present (W i) (μ i) (ρ i) (hi.2.2.1)) (v i)).symm
 exact ⟨(h.tends hz).eventually (lt_mem_nhds zero_lt_one),TaylorCap.process _ (Real.contDiffAt_log.mpr one_ne_zero) h hz hb hx⟩
end
end YM.QuadraticLocal.Aperture.Sage
