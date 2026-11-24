import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Sables
import YM.LocalLTE.Inset.Lapidary

/-! Taylor formula on the SAMUEL inset (one step schedule and virtual
comparison torus). Use cleanLog order t both ways. Keep shared conditional
vacuum determinant and ring scalar. No translational averaging yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Inset
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (A : ChartRatio G)
    (ρ : Bid.Dir G c→AxisChart G F) (D : ℝ) (β α : ℝ) (k : S.Choices) (p : ℕ)
local notation "Xs" => Positions (Uniform.Primary c G)

def joint := cleanLog (Lapis.table F k T.up T.high) (Lapis.mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) D

def song (g : ℝ) (x : Xs) :=
    stem (p+1) (joint F T A ρ D k) (g,x) + g⁻¹^2 * stem (p+3) (cedar F T ρ k) x + stem (p+1) (shed F T A ρ α k) x

lemma smoothSong (g : ℝ) (n : ℕ) : ContDiff ℝ (↑ n) (song F T A ρ D α k p g) :=
    (((stem_contDiff _ _).comp (contDiff_const.prodMk contDiff_id)).add
      (contDiff_const.mul (stem_contDiff _ _))).add (stem_contDiff _ _)

variable {σ C Λ u M P a c₀ c₁: ℝ} {j n : ℕ} {inc : BudgetPoint}
local notation "φ" => joint F T A ρ D k
variable (hD:Golf (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (gram F T.up T.high ρ k) n D u u P) (hT:T.down.Bounds T.low σ C Λ)
    (J₀ : BareRates.pre G σ C n) (hs:1 ≤ M) (ht : (Fintype.card (Uniform.Primary c G):ℝ)≤ M)
    (hj : j ≤ n) (he : p+3 ≤ n) (hx : 0 < a) (hu : a≤u)
    (hq : ∀ x∈ ball (0:ℝ×Positions (Uniform.Primary c G)) u, Brush n c₁ 1 (joint F T A ρ D k) x)
    (hg:0<β) (hb:gStep β < a)

include hD hT J₀ hs ht hj he hu hx hq hg hb
set_option maxHeartbeats 300000 in
theorem refrain (x : Xs) (hh:x∈ ball 0 a) (hΔ : Brush j c₀ 1 (lack F T A inc ρ β k D) x) :
    let b := (c₁*a^(p+1) + c₀ + β * (kinBill n J₀ T.low M P * a^(p+3))) + cryo J₀ T.low M P α Λ*a^(p+1)
    Brush j b a⁻¹ (fun x=> harmony T inc β α x - (Real.log (solar F A β) + song F T A ρ D α k p (gStep β) x)) x := by
  intro b; let g:= gStep β; let y:=(g,x)
  have ho: (0:Xs)∈ ball 0 u:=mem_ball_self hD.pos
  have hz₀ := Shellac.sticks F T A ρ k hD hT J₀ hs ht; have hη := Shellac.hills F T A ρ α k hD hT J₀ hs ht
  have ht' : a ≤ 1 := hu.trans hD.small
  let fee := kinBill n J₀ T.low M P
  let fe := cryo J₀ T.low M P α Λ
  have hf : 0 ≤ fee := (norm_nonneg _).trans ((hz₀ _ ho).2 (p+3) he (by omega))
  have hf' : 0 ≤ fe:= (norm_nonneg _).trans ((hη _ ho).2 (p+3) he (by omega))
  let U: ball (0:Xs) a ⊆ ball 0 u := ball_subset_ball hu
  have hk:= pays hx ht' hf he (fun i hi=> (hz₀ i (U hi)).1) (fun i hi j hj hm=> (hz₀ i (U hi)).2 _ hm (by omega)) x hh|>.smaller hj
  have he': p+1≤n:=by omega
  have hE:= pays hx ht' hf' he' (fun i hi=> (hη i (U hi)).1) (fun i hi j hj hm=> (hη i (U hi)).2 _ hm (by omega)) x hh|>.smaller hj
  have h₀ : ∀ x∈ ball (0:ℝ×Xs) a, Brush n c₁ 1 φ x:=fun x hx=> hq x (ball_subset_ball hu hx)
  have hd:= gS _ hg; have hy : y∈ ball (0:ℝ×Xs) a:= mem_ball_zero_iff.mpr (max_lt (show ‖g‖<a from (Real.norm_of_nonneg hd.1.le) ▸ hb) (mem_ball_zero_iff.mp hh))
  have hP:= pays hx ht' (h₀ _ hy|>.nonneg) he' (fun x hx=> (h₀ x hx).smooth) (fun x hx i _ hi=> (Brush.offer.1 (h₀ x hx)).2 i hi) y hy |>.smaller hj
  have hP' : Brush j (c₁*a^(p+1)) a⁻¹ ((φ-stem (p+1) φ)∘ arc g) x:= by
    have hx (y:Xs): arc g y=(g,0)+hook _ y:=by simp
    let Q:= φ-stem (p+1) φ
    change Brush _ _ _ (Q ∘ arc g) x
    rw [show Q ∘ arc g=(fun x=>Q ((g,0)+hook _ x)) from funext fun y=> congr_arg Q (hx y)]; exact skim _ ((hx x) ▸ hP) n_hook
  have hA:= hk.smul β; rw [Real.norm_of_nonneg hg.le] at hA; have hB:= hΔ.climb le_rfl ((one_le_inv₀ hx).2 ht')
  apply (((hP'.gathering hB).gathering hA).gathering hE).shimmy
  have hv:g⁻¹^2=β:= by
    rw [inv_pow,inv_eq_iff_eq_inv]; exact (mul_inv_cancel_right₀ hg.ne' _).symm.trans (show _ from (by rw [show g^2*β=1 from hd.2,one_mul]))
  refine Eventually.of_forall (fun i=>?_)
  change harmony T inc β α i - (Real.log (solar F A β)+(stem (p+1) φ (g,i) + g⁻¹^2 * stem (p+3) _ i + stem (p+1) _ i)) = ((φ (g,i) - stem (p+1) φ (g,i) + lack F T A inc ρ β k D i) + β * (cedar F T ρ k i-stem (p+3) _ i)) + (shed F T A ρ α k i-stem (p+1) _ i)
  rw [Shellac.merit F T A inc ρ β α k i (D:=D),hv,show pigment F T A ρ β k D i=φ (g,i) from rfl]; ring
end YM.LocalLTE.Inset
