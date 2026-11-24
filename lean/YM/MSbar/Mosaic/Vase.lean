import YM.MSbar.Mosaic.Province
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk
variable {G:Gauge}
namespace Issue
variable {ϑ:Type} {X:ϑ→ℝ}{A:ϑ→Issue G}{f:ϑ→ℝ}{φ:Filter ϑ}(hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage) (K:Patch)(D:KernelChoices)
variable (hG:G.Simple)
local notation "Y"=> (fun i:ϑ=> tip G K.L (X i))
local notation "u!" i=> (A i)
local notation "D'" i=> (A i).f
local notation "g'" i=> (A i).c
local notation "L"=> fun i:ϑ=> tip G K.L (X i)
structure Paid (A:Issue G)(K:Patch)(H H':Stage)(J:Voice G) (x:ℝ): Prop where
    space : A.S.patch=K
    payments : Season J H H' x A.pre A.post A.S (courage G K.L x)
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i))
local notation "t"=> (fun i:ϑ=>(A i).fClock)
local notation "s"=> (fun i:ϑ=>(A i).cClock)
include hX hp hG
lemma tails : ∀ᶠ i in φ, lensT (tip G K.L (X i)) (A i).fClock ∧ lensT (X i) (A i).cClock :=by
     filter_upwards [hp,hX.eventually_gt_atTop 0,((Work.E09.betaF_growth G K.L).comp hX).eventually_gt_atTop 0] with i hi hx he; have hT:=hi.payments.case_; rw [hi.space] at hT; exact ⟨ever he hT.beta hT.upper,ever hx hi.payments.hull.beta hi.payments.hull.upper⟩
lemma roundS: Run φ (Y) (fun i=>(A i).fClock) (-(1/2)) ∧ Run φ (Y) (fun i=> ((A i).fClock)⁻¹) (1/2)∧ Run φ X (fun i=>(A i).cClock) (-(1/2)) ∧ Run φ X (fun i=>((A i).cClock)⁻¹) (1/2):=by
     have he:= (tails hX J H H' K hG hp).mono (fun x h=> h.1); let hp':= (charges (X:=Y) ((Work.E09.betaF_growth G K.L).comp hX) he)
     exact ⟨hp'.1,hp'.2,charges hX ((tails hX J H H' K hG hp).mono fun x h=>h.2)⟩
-- Sensor within.Effort masks
variable (P:Palisade)(W:(i:ϑ)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
local notation "P₀" i=> (A i).fClock • W i
include hW
lemma shapeK: ∀ᶠ i in φ, ‖(A i).fClock • W i‖ ≤ skies (tip G K.L (X i)) ∧0<(A i).fClock∧(A i).fClock≤1∧shade G*|(A i).fClock| *‖W i‖ ≤1 :=by
    let S:= fun i:ϑ=> tip G K.L (X i); have hs:Tendsto S φ atTop:= (Work.E09.betaF_growth G K.L).comp hX; have ht:=tails hX J H H' K hG hp; have hv:Run φ X (fun i=> hull (X i)) 0:=(Run.stanza hX|>.mulY hX (32:ℝ)⁻¹).mulK hX 4; have hx: Run φ X t (-(1/2)):= (Run.wander hX G hG K.L _ t).2 (roundS hX J H H' K hG hp).1; have he: Tendsto t φ (𝓝 0):= hx.bouquet hX (by norm_num); let A':= hx.mulK hX (shade G)
    filter_upwards [hW,ht, hs.eventually_gt_atTop 1, he.eventually (ge_mem_nhds zero_lt_one), ((A'.Yrat hX hv).bouquet hX (by norm_num : -(1/2:ℝ)<0)).eventually (ge_mem_nhds zero_lt_one),hX.eventually (Alto.drift_scale hG K.L)] with i hv hx Hc he hg hY
    let v:= S i; let z:= Real.log v; have hz:0<z:= Real.log_pos Hc; have hh: hatW (X i) ≤ z^2:= hY.2.1; have h0:0<v:=zero_lt_one.trans Hc; have hE:0<cue v:=by unfold cue; positivity
    have hQ : 0 < (A i).fClock:= (half_pos hE).trans_le hx.1.1; have hG:= (norm_nonneg _).trans hv
    refine ⟨?_,hQ,he,?_⟩; · rw [norm_smul,Real.norm_of_nonneg hQ.le]; refine le_trans (mul_le_mul hx.1.2 hv (norm_nonneg _) (show 0 ≤ _ from (by exact (mul_pos zero_lt_two hE).le))) ?_; change 2*cue v*hull (X i) ≤ v^(-(1/2:ℝ))*z*z; rw [Real.rpow_neg h0.le,← Real.sqrt_eq_rpow]; unfold Mosaic.hull Mosaic.vol; change _ ≤ cue v*z*z; nlinarith only [mul_le_mul_of_nonneg_left hh hE.le,mul_nonneg hE.le (sq_nonneg z)] -- parse z not unfolded
    rw [abs_of_pos hQ]; exact (mul_le_mul_of_nonneg_left hv (mul_nonneg (shade_pos G).le hQ.le)).trans hg
-- port.Exact book via sequences. Φ lhs.Stock.ClockD inputs. Precision unifier. Further next.
end Issue
end YM.MSbar.Mosaic
