import YM.OPE.Compatible.Gems.Core
/-! # Smooth local dec.Marg projections on every subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Progress.StationaryScenes Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T) (Y:Studio L) (J:Finset (Rubric G Y.X))
local notation "Fθ"=> L.ForestQ
abbrev Hκ (Y:Studio L):= PatchM L.Z L.H L.A L.U L.k L.F Y.X
noncomputable abbrev axY :Rubric G Y.X → Module.Dual ℝ Y.St := castAt (Limn.Tip G (↥Y.X))
noncomputable abbrev Pip := LinearMap.pi (fun i:(J:Type)=>axY L Y i.val)
local notation "A!"=> Pip L Y J
local notation "L!"=> Hκ L Y
lemma prox (i:(J:Type)): A! (Limn.Tip G (↥Y.X) i.val)= Pi.single i 1:=by
              funext j; change cash (Limn.Tip G (↥Y.X)) (Limn.Tip G (↥Y.X) i.val) j.val= _; rw [cashOne]; by_cases h:j=i
              · subst j; simp
              rw [Pi.single_eq_of_ne (show j.val≠i.val from fun ht=>h (Subtype.ext ht)),Pi.single_eq_of_ne h]
lemma pros : Surjective (A!):=by
        intro y; let v(i:(J:Type)):= Limn.Tip G (↥Y.X) i.val; let L':= A!; refine ⟨∑ i,y i • v i,?_⟩; change L' _ = _; rw [_root_.map_sum]; funext i; rw [Finset.sum_apply]; simp_rw [_root_.map_smul L',Pi.smul_apply,show ∀ i, L' (v i)= Pi.single i 1 from prox L Y J]; rw [Finset.sum_eq_single i]; simp; exact fun j _ h=>by rw [Pi.single_eq_of_ne (Ne.symm h), smul_zero]
        exact fun hx=>False.elim (hx (Finset.mem_univ _))
noncomputable abbrev Boat:= claspR L! A! (pros L Y J)
noncomputable abbrev Pier := Swear.ren A! (Boat L Y J)
local notation "μ"=>Y.μφ
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0 < e)
include h ht hc he
lemma tollπ (i:(J:Type)) : ∃ p,A! p= Pi.single i 1 ∧ (L!).P p p≤limbC G s c :=by
          let p:= Limn.Tip G (↥Y.X); refine ⟨p i.val,prox ..,?_⟩; have hx:= WithK L.Z L.ForestQ Y.X L.Fund L.F.L.Q L.F.P0 (p i.val) (p i.val); have hv:= Chan ((h.principal ht hc he (shout G Y.X)).1) i.val i.val; rw [hx,cashOne]; simp; simp only [Green.wt,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at hv; exact (le_abs_self _).trans hv -- hx defeq
lemma LapK (i:Rubric G Y.X)(hq:∀ j:(J:Type),t≤ separation (pointK L.Z Fθ (shout G Y.X i)) (pointK L.Z Fθ (shout G Y.X j.val))) (k:ℕ)(hk:1 ≤ k) :
      let a':= (((Fintype.card (J:Type):ℝ)*Real.sqrt (limbC G s c))*(C*Real.exp (-(u*t))))*ampleP k; Fault (Amalg (Hκ L Y) (Chart.tangent G (Y.X:Type))) k ((axY L Y i ∘ Prod.fst)- (axY L Y i ∘ Pier L Y J)) (a'+a'):=by
          intro a'
          refine stickV L! A! (pros L Y J) (t:=limbC G s c) (?_) _ (axY L Y i) ?_ (mul_nonneg h.vein.broad.le (Real.exp_nonneg _)) (palmPos _ hc _) k hk --args
          · intro j; exact tollπ L Y J h ht hc he j
          intro j; have hz:= h.Cov_E ht hc he Y.X i j.val; let v:= separation (pointK L.Z Fθ (shout G Y.X i)) (pointK L.Z Fθ (shout G Y.X j.val)); let A:= (Hκ L Y).wick (axY L Y i) (axY L Y j.val); change |(Hκ L Y).wick (axY L Y i) _| ≤ _; rw [show LinearMap.proj j ∘ₗ Pip L Y J=axY L Y j.val from LinearMap.ext fun x=> rfl, Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]; change |A| *_ ≤_; change Real.exp (u*(v:ℝ))*|A|≤C at hz; rw[mul_comm]; exact le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (hq j) h.vein.warmth.le)) (abs_nonneg _)) hz
end
end YM.OPE.Borealis.Galea
