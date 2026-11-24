import YM.RG01Estimate.Abacus
/-!
 # Ordinary coefficient comparison input: versions with torus discrepancies.

   Independent model, its smooth render, p_i horizon and jet discrepancy
   estimates must be supplied. This file implements the analytic bills *from*
   identification of ordinary jets. `ψ` is the candidate stripped floor
   (`β*mainTerm T.low T.down + γ*secondTerm ... + unmasked loop + ALL
    formal extra logarithmic entries`). Maybe including re-expansion costs,
   depending on comparison setup. We require that floor at the operational
   kernel β, charge it against a finite-order analytic model of said rendered
   terms scaled by β⁻¹. Estimates hold for any such grade comparison (for
   example extra kinetic uncertainties/separate reset investment can be held
   explicit). `dec` / `Card.columns` quantifies modulo *explicitly separate
   scalar*; no assertion on sizes of the unmasked constants in the canonical
   truncation. This does NOT estimate a raw extensive remainder as flat and
   does not work with a numerator at a substitute coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Promise
open Function Filter Set Metric Finset Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior Abacus
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}
section grade
-- generic beta-affine price without summing dimensions.
variable {X:Type} (a b : X→ℝ)
def raise (P:Policy X ℝ) : Policy X ℝ:= fun i=> if 2 ≤ i then P (i-2) else 0
lemma raises (P:Policy X ℝ)(r:ℕ)(β:ℝ) (h:0<β) (x:X):
    β*Series.trunc (raise P) (gStep β) (r+2) x = Series.trunc P (gStep β) r x:= by
   let b:=gStep β; let f(r:ℕ) :=Series.trunc (raise P) b r x
   induction r with
   | zero=>simp [Series.trunc,raise,sum_range_succ]
   | succ r ih=>
      unfold Series.trunc; nth_rw 1 [show r+1+2=r+2+1 by omega,Finset.sum_range_succ]; rw [Finset.sum_range_succ _ r,mul_add]
      apply congr_arg₂ (·+·) ih; rw [raise,if_pos (show 2≤r+2 by omega),Nat.add_sub_cancel,pow_add]
      have hk:= Fare.gS β h; simp only [smul_eq_mul]; linear_combination (gStep β^r*P r x)*hk.2
lemma shifted [NormedAddCommGroup X] [NormedSpace ℝ X] (C:Policy X ℝ)(r:ℕ) (β:ℝ) (h:0<β)(hp:gStep β≤1) (x:X)
    (n:ℕ)(δ:ℝ)(hδ:∀ i<r+2, Brush n δ 1 (fun y=> C i y-C i 0) x):
    Brush n (β*((r+2:ℕ)*δ)) 1 (fun y=> β*(Series.trunc C (gStep β) (r+2) y-Series.trunc C (gStep β) (r+2) 0)) x := by
    let b:=gStep β; have he :0<b:=(gS β h).1; let W:= ∑ i∈range (r+2),δ
    have hY:W=(r+2:ℕ)*δ:=by simp [W]
    have hB: Brush n W 1 (fun y=>∑ i∈range (r+2), b^i • (C i y-C i 0)) x:= by
         apply Brush.spree _ _ _ zero_le_one; intro i hi
         have hk:=hδ i (mem_range.mp hi)
         apply (hk.smul _).climb _ le_rfl; rw [Real.norm_of_nonneg (pow_pos he _).le]; exact mul_le_of_le_one_left hk.nonneg (pow_le_one₀ he.le hp)
    have hx:= hB.smul β; rw [Real.norm_of_nonneg h.le,hY] at hx; refine hx.shimmy ?_
    filter_upwards with y; unfold Series.trunc; simp only [smul_sub,Finset.sum_sub_distrib]; rw [← smul_sub]; rfl
-- suffices to pay discrepancy at each grade's own price.
lemma priced [NormedAddCommGroup X] [NormedSpace ℝ X] (C:Policy X ℝ)(r:ℕ) (β:ℝ) (h:0<β) (x:X)
    (n:ℕ)(δ:ℝ)(hδ:∀ i<r+2, Brush n δ 1 (fun y=>gStep β^i •(C i y-C i 0)) x):
    Brush n (β*((r+2:ℕ)*δ)) 1 (fun y=> β*(Series.trunc C (gStep β) (r+2) y-Series.trunc C (gStep β) (r+2) 0)) x := by
    let b:=gStep β; let W:= ∑ i∈range (r+2),δ
    have hY:W=(r+2:ℕ)*δ:=by simp [W]
    have hB: Brush n W 1 (fun y=>∑ i∈range (r+2), b^i • (C i y-C i 0)) x:= by
       apply Brush.spree _ _ _ zero_le_one; intro i hi; exact hδ i (mem_range.mp hi)
    have hx:= hB.smul β; rw [Real.norm_of_nonneg h.le,hY] at hx; refine hx.shimmy ?_
    filter_upwards with y; unfold Series.trunc; simp only [smul_sub,Finset.sum_sub_distrib]; rw [← smul_sub]; rfl
end grade
variable {c f:Side}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
      (k:S.Choices)(r:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)(t:ℝ)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable (ψ:Config G c→ℝ) (v:ℝ× Positions (Uniform.Primary c G)→ ℝ)(H: Poll.Body (Precision.Key F G)→ ℝ × Positions (Uniform.Primary c G)→ℝ)(j:ℕ)

def dec : Policy X ℝ:= RealTaylor.piece v- RealTaylor.piece (Stellar.pressure F T k r) +
      raise (Series.logarithm (Laplace.vintage F T k r O H) j-RealTaylor.piece (entropy F T k r O))

local notation "e" => dec T F k r O v H j
variable {s n:ℕ}{β y u δ σ θ α : ℝ} (x:Positions (Uniform.Primary c G))
local notation "b" => gStep β
structure Card (n:ℕ)(B:BudgetPoint)(β y u δ σ:ℝ):(Prop) where
    pays x : x ∈ corridor u (ball (0:Positions (Uniform.Primary c G)) y) → Brush (n+(j+2)) σ 1 v x
    model (x : Positions (Uniform.Primary c G)) : x∈ ball 0 y → actual (gStep β • x)∈ Boulevard.sunny B → ψ (actual (gStep β • x))=β*v (gStep β,x)
    eligible : gStep β < u
    columns (x : Positions (Uniform.Primary c G)) : x∈ball 0 y → ∀ l<j+2, Brush n δ 1 (fun y=> gStep β^l • (dec T F k r O v H j l y-dec T F k r O v H j l 0)) x

def coins :ℝ:= Real.log (solar F O β)-Lantern.shade (Lapis.gram F T.up T.high r k) 0 + β*Series.trunc (dec T F k r O v H j) (gStep β) (j+2) 0
lemma scroll (hp:0<β):
     β*(Series.trunc (dec T F k r O v H j) b (j+2) x-Series.trunc (dec T F k r O v H j) b (j+2) 0) =
     Laplace.report F T k r O β H j x + β*RealTaylor.trunc v (j+2) b x - coins (β:=β) T F k r O v H j := by
   let g' i x:= e i x; let W:= Series.logarithm (Laplace.vintage F T k r O H) j; let V:=entropy F T k r O; let A:=Stellar.pressure F T k r
   have h : β*Series.trunc g' b (j+2) x =β*RealTaylor.trunc v (j+2) b x- β*RealTaylor.trunc A (j+2) b x + (Series.trunc W b j x-RealTaylor.trunc V j b x) := by
      let U:=W- RealTaylor.piece V
      have hg : Series.trunc g' b (j+2) x= RealTaylor.trunc v (j+2) b x- RealTaylor.trunc A (j+2) b x + Series.trunc (raise U) b (j+2) x:= by
         unfold Series.trunc RealTaylor.trunc; rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]; apply sum_congr rfl
         intro i hi; rw [← smul_sub,← smul_add]; rfl
      rw [hg,mul_add,mul_sub,raises U j β hp]; unfold Series.trunc RealTaylor.trunc; rw [← sum_sub_distrib]; congr; ext i; simp only [← smul_sub]; rfl
   unfold coins Laplace.report Stellar.model; rw [mul_sub]; change β*Series.trunc g' _ _ _ - _=_; rw [h]; unfold A W V; ring

variable (U:Config G f→ℝ) (h:Card T F k r O ψ v H j n B β y u δ σ) (hy : Brush n (gStep β^j*θ) 1 (fun x=> Laplace.vacuumS (S:=S) β U x-Laplace.report F T k r O β H j x) x)

-- actual prefix and its budget at ALL sunny x of specified aperture. price scalar drift.
def action (β:ℝ) (m:Config G c) := Real.log (S.push β U m)+ψ m
include h hy in
lemma hatch (hp:0<β)(_hm:b≤1)(hq:x∈ ball 0 y)(hz: actual (b • x)∈ Boulevard.sunny B):
    Brush n ((b^j*θ + b^j*σ) + β*((j+2:ℕ)*δ)) 1 (fun x: Positions (Uniform.Primary c G)=> Promise.action (S:=S) ψ U β (actual (b • x))- coins (β:=β) T F k r O v H j) x := by
   have hh : 0<b:= (Fare.gS β hp).1
   have ht:=RealTaylor.priced_defect v (ball (0:X) y) u isOpen_ball b x (show (b,x) ∈ corridor u _ from ⟨mem_ball_zero_iff.mpr (by rw [Real.norm_of_nonneg hh.le]; exact h.eligible),hq⟩) (j+2) h.pays
   have hr:= ht.smul β; rw [Real.norm_of_nonneg hp.le,abs_of_pos hh] at hr
   rw [show β*(b^(j+2)*σ)=b^j*σ by rw [pow_add]; linear_combination (b^j*σ)*(Fare.gS β hp).2] at hr
   have hb:= priced (C:=e) j β hp x n δ (h.columns _ hq)
   have hx : ContinuousAt (fun y:X=> actual (b • y)) x:= by apply Continuous.continuousAt; apply continuous_pi; intro i; simp_rw [actual,Work.F03.represent_link]; fun_prop
   refine ((hy.gathering hr).gathering hb).shimmy ?_; filter_upwards [isOpen_ball.mem_nhds hq,hx (Boulevard.sky B|>.mem_nhds hz)] with x' hY hx'
   have hh := h.model x' hY hx'
   change action (S:=S) ψ U β (actual (b • x')) - _=(_+β* _)+β*( _-_)
   unfold action; rw [hh,scroll T F k r O v H j x' hp]; change Real.log (S.push β _ _)+_-_=(Real.log (S.push β _ _)-_+_)+_; ring -- x'.cost

end YM.RG01Estimate.Promise
