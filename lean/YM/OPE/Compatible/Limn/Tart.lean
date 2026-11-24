import YM.OPE.Compatible.Limn.Press
/-! # Exterior orthogonal omission in paired Gaussian -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X Y V:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
open Green (wt)
section
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][Fintype Y]
lemma ultra (Z:Law X)(p q:Y→ Module.Dual ℝ X)(a c:Y→ℝ) (hR:0 ≤ R)(hp: (∑ i,|a i|) ≤ t)(hq:(∑ i,|c i|) ≤ ε)(hv:∀ i j, ‖Z.wick (p i) (q j)‖ ≤ R): ‖Z.wick (∑ i,a i • p i) (∑ i,c i • q i)‖ ≤ (t*ε)*R:=by
       unfold Law.wick; rw [map_sum Z.inverse,LinearMap.sum_apply]; refine (norm_sum_le ..).trans ?_
       have ht: 0 ≤ t:=(sum_nonneg (fun i _=>abs_nonneg _)).trans hp
       have hk(j:Y): ‖(c j • q j) (∑ i,Z.inverse (a i • p i))‖ ≤ |c j| *(t*R):=by
            rw [LinearMap.smul_apply,norm_smul, Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); rw [map_sum]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right hp hR); rw [sum_mul]; apply Finset.sum_le_sum; intro i _; rw [Z.inverse.map_smul,(q j).map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (hv i j) (abs_nonneg _)
       apply (sum_le_sum fun i _=>hk i).trans;rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right hq (mul_nonneg ht hR)).trans_eq (by ring)
end
section
variable (B: Matrix (Key F G) (Key F G) ℝ)(I: Seats F) (Z: Law (AxisChart G F))(h:Trained (countingBasis F G) B Z)(hB:B.PosDef)
local notation "R!"=>Rubric G I
local notation "K!"=>Key F G
local notation "J!"=>countingBasis F G
local notation "Tp"=>Tip G (I : Type)
def Stanza (p:Rubric G I)(ε:ℝ):Prop:=∀ y: Key F G, dark I y → ε ≤ separation (pointK S F (shout G I p)) (pointK S F y)
noncomputable def Δp (p:Rubric G I):Module.Dual ℝ (AxisChart G F) := (castAt (Tip G (↥I)) p ∘ₗ (ChartUp S F I Z).toLinearMap)- castAt (countingBasis F G) (shout G I p)
noncomputable def krp (i:R!)(j:K!):= if dark I j then clipRail S F I B i j else 0
include h hB
lemma rat (i:R!): Δp I Z i=∑ j:K!, krp B I i j • castAt J! j:=by
       apply LinearMap.ext; intro p; rw [LinearMap.sum_apply]; change cash Tp (ChartUp S F I Z p) i - cash J! p (shout G I i)= _; rw [Adu B I Z h hB,add_sub_cancel_left]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [krp,LinearMap.smul_apply]; split
       · rfl
       simp
variable {s:ℝ}(hp:Pours (clipRail S F I B) (pointK S F ∘ shout G I) (pointK S F) t s)(he:0 < t)(p:Rubric G I)(hz:Stanza I p ε)
omit h hB
include hp hz he
lemma ton : ∑ i: Key F G,|krp B I p i| ≤ Real.exp (-(t*ε))*s:=by
        have he' := CoverSlip (p:=pointK S F) (A:=clipRail S F I B) (dark I) he hp p hz; rw [← Finset.sum_congr rfl (g:=fun i=>|krp B I p i|) (f:=fun i=> if dark I i then ‖clipRail S F I B p i‖ else 0) (fun i _=>by unfold krp; split <;> simp [Real.norm_eq_abs])]; exact he'
include h hB
lemma repD (x:AxisChart G F): ‖Δp I Z p x‖ ≤ Real.exp (-(t*ε))*s*‖x‖:=by
      rw [rat B _ Z h hB,LinearMap.sum_apply]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (ton B I hp he p hz) (norm_nonneg x)); rw [sum_mul]; apply sum_le_sum; intro i _; rw[LinearMap.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (Cast_price x i) (norm_nonneg _)
lemma repV (hK:∀ i j: K!,‖B⁻¹ i j‖ ≤r) (hx:0 ≤ r): ‖Z.wick (Δp I Z p) (Δp I Z p)‖≤ (Real.exp (-(t*ε))*s)^2*r :=by
       rw [rat B I Z h hB,sq]; apply ultra _ _ _ _ _ hx (ton ..) (ton ..); · intro i j; rw [coverage J! Z h hB]; exact hK ..
       all_goals assumption
end
end YM.OPE.Limn
