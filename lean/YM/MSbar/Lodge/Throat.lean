import YM.MSbar.Lodge.Dawn
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c n:Side}{M:Type}[MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]{p k m D':ℕ}{w v V Y Y' C B u η a b D ε:ℝ}
open MeasureTheory Set Metric Cane Laurent Bloch
local notation "U"=> Primary n G
local notation "T"=> Primary c G
local notation "A"=> Positions (Primary n G)
local notation "X"=> Positions (Primary c G)
local notation "L"=>Measuring.chart n G
local notation "L'"=>Measuring.chart c G
variable (r:Ratio c n) (P: Cross r.count (TypeFace 1) (TypeFace 1)) (h:Cane P D η a B D' p)(hb:a/(r.count.val:ℝ) ≤ b)
variable {F:Positions (Primary n G)→ℝ}{f:ℝ→ℝ}(hF:Vase F k C w)(hf:Hat k w V f)(hw:0<w)(Q:Positions (Primary c G)→L[ℝ] Positions (Primary n G))
local notation "Π"=> roll r P G
local notation "R"=>(r.count.val:ℝ)
variable (he:JetTab (Measuring.chart n G) b p w (Metric.closedBall 0 w) F m Y)(hp:m+1≤k)
variable (W:M→ Positions (Primary n G))(hW:Measurable W)(x:Positions (Primary c G))
local notation "S"=> Clamp f ∘ (fun v=> W v+Q x)
local notation "Ω"=> Cane.value a D η B p D'
include h hb hF hf hw hW
include he hp
lemma throat : ∃ Z:List (Primary c G)→ℝ, (∀ i:Primary c G,∀ l:List T,l.length=m→∀ (W:M→Positions (Primary n G))(x: X),Measurable W→ |waltz (roll r P G) μ F (Clamp f ∘ (fun y:M=>W y+Q x)) (i::l)|≤ Z (i::l))∧ summit (Measuring.chart c G) a p Z m (Y/w^(m+1)* R^4*(Cane.value a D η B p D'/R)^(m+1)):=by
     obtain ⟨Z,hZ,hY⟩:= primer (μ:=μ) Q hf hF W hW hw.le L hw hp he
     let X' := pension r P G []; let E(t:List T):= ter (m+1) X' Z t; refine ⟨E,fun i l hp W x hW=>?_,fun i=>?_⟩
     · let K:= Clamp f ∘ (fun y:M=> W y+Q x); have hh: (i::l).length=m+1:=by rw [List.length_cons,hp]
       unfold waltz shaft; rw [hh]; simp_rw [vin]; refine (polished ..).trans (shiny m.succ (fun v hL=>?_)); rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hZ _ hL|>.2 W x hW) (abs_nonneg _)
     have hg(k):=hY k; have hZ'(k): Yarn m (fun v:List U=> Z (k::v)*swipe L b p (k::v)) ≤ Y/w^(m+1):= (le_trans (le_of_eq (stitch _ (g:=fun t=> |Z (k::t)| *swipe L b p (k::t)) (fun i hi=>by rw [abs_of_nonneg (hZ _ (by rw [List.length_cons,hi])|>.1)]))) (hg k))
     refine le_trans (le_of_eq ?_) (show Yarn m (fun l:List T=> _ )≤ _ from Measuring.thin P i h (div_nonneg he.1 (pow_pos hw _|>.le)) hb Z (fun l hl=> hZ l hl|>.1) hZ'); refine stitch _ fun t ht=>?_ ; rw [abs_of_nonneg (show 0 ≤ E _ from (by unfold E ter; refine luster _ fun k h=>?_ ; exact mul_nonneg (hZ k h|>.1) (abs_nonneg _)))];exact mul_comm .. -- orientation discrepancy grouping?
omit he hp
variable (hk: JetTab (Measuring.chart n G) b p w (Metric.closedBall 0 w) F (m+1) Y)
include hk
lemma glare (he:m+2≤k)(hp:∀ i:Primary n G,Integrable (fun y:M=>|W y i+(Q x) i|) μ∧ (∫ y:M, |W y i+(Q x) i|∂μ) ≤u)(hu:0≤u)(hb':0≤b):
    summit (Measuring.chart c G) a p (fun t=> waltz Π μ F (Clamp f ∘ (fun y:M=> W y+Q x)) t-buoy (F∘Π) 0 t) m ((u*Y/w^(m+2))*R^4*(Cane.value a D η B p D'/R)^(m+1)):=by
    let z:= S; let t'(i:List U):=pearl F z i μ-buoy F 0 i; have hv : summit (Measuring.chart n G) b p t' m (u*Y/w^(m+2)):= dawn Q hf hF W hW x hw.le L hw he hk hp hu hb' -- check
    have ht: ContDiffAt ℝ k F (Π 0):=by rw [map_zero]; exact hF.smooth _ (mem_closedBall_self hw.le)
    let K:= pension r P G []; let Z(t: List T):= ter (m+1) K (fun i=>|t' i|) t; intro i; refine le_trans ?_ (show Yarn m (fun v:List T=> swipe L' a p (i::v)*ter (m+1) _ _ (i::v)) ≤ _ from Measuring.thin P i h (div_nonneg (mul_nonneg hu hk.1) (pow_pos hw _|>.le)) hb (fun i=>|t' i|) (fun _ _=> abs_nonneg _) (fun _=>hv _))
    refine shiny _ fun v hh=> ?_; dsimp only; rw [Lis.paint F Π (i::v) 0 k ht (by rw [List.length_cons,hh]; omega),map_zero]; have hl:(i::v).length=m+1:=by rw [List.length_cons,hh]
    unfold waltz shaft; simp_rw [vin]; rw [hl, show Yarn _ _- Yarn _ _= Yarn (m+1) (fun l:List U=> t' l * beads K l (i::v)) from ?_,mul_comm (abs (Yarn _ _)) _]; swap
    · apply sub_eq_iff_eq_add.mpr; rw [←pockets]; refine stitch _ fun k hk=>?_ ; unfold t' z K; ring
    exact mul_le_mul_of_nonneg_left ((polished ..).trans (le_of_eq (by unfold ter; exact stitch _ fun l _=> abs_mul ..))) (effect ..|>.le)
end YM.MSbar.Lodge
