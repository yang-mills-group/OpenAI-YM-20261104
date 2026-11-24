import YM.RG01Estimate.Promises
/-!
 # Pay the auxiliary bill at all sunny cells and reissue its signal price
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
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}
variable {c f:Side}{A:Listing G c}{S:StepData c f}(T:Tube G S)(F:Forest S.ratio)(B:BudgetPoint)
      (k:S.Choices)(r:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)(t:ℝ)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable (ψ:Config G c→ℝ) (v:ℝ × Positions (Uniform.Primary c G)→ ℝ)(H:Poll.Body (Precision.Key F G)→ ℝ× Positions (Uniform.Primary c G)→ℝ)
    {L:Side} {R a i d j:ℕ} {β τ m y u δ σ θ α γ ℓ γ₁ W V n d' D w v' s s' C C' P' : ℝ}
local notation "b" => gStep β
variable (U:Config G f→ℝ) (x: Positions (Uniform.Primary c G))
section earn
variable {F':Collection.Source G c}{P U' V': ℕ→ Config G c→ℝ} (A':Rack A a U')

-- Tested full candidate forecast: γ*α components & pre-reset β. path data drawn on S.
def forecast (P:ℕ→ Config G c→ℝ)(β γ:ℝ)(M:Config G c):= β*mainTerm T.low T.down M + γ*secondTerm T.low T.down M + Precision.loop T.down M + Boulevard.throng P M

variable (h : ∀ Z,S.push β U Z=earlyValue A T.down T.low B F' β θ γ Z)
    (hf:F'.logRead=P+V'+U')(he: Meadow.Budget B A.reg P v')(hU:Meadow.Budget B A.reg U' s)
    (hV:Meadow.Budget B A.reg V' s')(hT:T.down.Bounds T.low C C' P')
include h hf he hU hV hT
lemma header (Z:Config G c)(hZ: Z∈ sunny B): Promise.action (S:=S) (forecast T P β γ) U β Z=
     θ*(Fintype.card (Site c):ℝ)- Trio.froth A'.polygon Z - Boulevard.throng V' Z:= by
    have hr := smoky hZ; have hh:= h Z
    let A₀:= (A.read F'); have hv : A₀.gas B Z=1:= Activities.gas_one A₀ B hr
    let N:=revise F' P; let N':= revise F' (P+V'); let D:=revise F' V'; let X₀:=revise F' U'
    have ht': A₀.additive B Z= Boulevard.throng P Z + Boulevard.throng V' Z+ Trio.froth A'.polygon Z := by
       have h': F'=revise N' (P+V'+U'):= congr_arg₂ Collection.Source.mk hf rfl
       unfold A₀; rw [h']; rw [show (A.read (revise N' (P+V'+U'))).additive B Z=(A.read N').additive B Z+(A.read X₀).additive B Z from adds_pow B Z (show Meadow.Budget B A.reg (revise F' (P+V')).logRead _ from pay_bundle B he hV) hU]; rw [raw_eq_of_empty,show (A.read X₀).additive B Z=Trio.froth A'.polygon Z from (raw_eq_of_empty B Z A X₀ hr).trans (show Boulevard.throng U' Z=_ from A'.throng B Z hr)]; swap; exact hr
       congr 1; rw [← raw_eq_of_empty B Z A _ hr]; exact (adds_pow B Z (show Meadow.Budget B A.reg N.logRead v' from he) hV).trans (congr_arg₂ (·+·) (raw_eq_of_empty B Z A N hr) (raw_eq_of_empty B Z A D hr))
    unfold action forecast; rw [hh]; have h': Collection.receipt T.down T.low B Z= secondTerm T.low T.down Z:= allGoodPrice hT Z hr
    unfold earlyValue RG.Rep.eval Collection.frozen RG.Rep.exponent; dsimp only
    unfold A₀ at ht' hv; rw [hv,mul_one,← Real.exp_add,Real.log_exp, Pane.crystalline _ _ _ _ _ hr, h', ht']; ring -- syntax
end earn
section cards
variable {B' : BudgetPoint} (h : Card T F k r O ψ v H R B.order B β y u δ σ) (hp:0<β)(hb:gStep β ≤ 1)
    (hx : ∀ x: Positions (Uniform.Primary c G), ‖x‖+1< y→ actual (gStep β • x)∈ Boulevard.sunny B→ Receipt.Article T F B' r t d' D y β s α x U H i j ∧ Receipt.Note T F B' k r O t d' D y β s α W w V n x i j R B.order)
    (hk : ∀ z:Poll.Body (Precision.Key F G),∀ x∈ ball (0:Positions (Uniform.Primary c G)) y,H z (0,x)=1)

include h hp hb hx hk
lemma near_price (hv: ‖x‖+1< y)(hZ : actual (b • x) ∈ sunny B) :
     Brush B.order ((b^R*V + b^R*σ) + β*((R+2:ℕ)*δ)) 1 (fun x: Positions (Uniform.Primary c G)=> Promise.action (S:=S) ψ U β (actual (b • x))- coins (β:=β) T F k r O v H R) x := by
   apply hatch
   case h => exact h
   case hp=> exact hp
   case _hm => exact hb
   case hz=> exact hZ
   case hq => exact mem_ball_zero_iff.mpr (by linarith only [hv])
   obtain ⟨hz,hy⟩:= hx _ hv hZ; exact (hy.charge _ _ hz hk).2.2

omit h hp hb hx hk in
lemma f_one : (1: Config G c)∈ sunny B:= by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos -- included issue
lemma still_bill (hv: ‖x‖+1< y)(hZ : actual (b • x) ∈ sunny B) : Brush B.order (2*((b^R * V+b^R*σ)+ β*((R+2:ℕ)*δ))) 1
      (fun x: Positions (Uniform.Primary c G)=> Boulevard.stillA (Promise.action (S:=S) ψ U β) (actual (b • x))) x:= by
   let W:= action (S:=S) ψ U β; let M:= coins (β:=β) T F k r O v H R
   let Z:= (b^R*V+b^R*σ)+ β*((R+2:ℕ)*δ)
   have h' (x':X) (hy : ‖x'‖+1< y)(hr: actual (b • x') ∈ sunny B):= near_price T F B k r O t ψ v H U x' h hp hb hx hk hy hr
   have he: actual (b • (0:X))=1:=by simp [Boulevard.actual]
   have hr:= h' 0 (by have ht:= norm_nonneg x; simp; linarith) (he ▸ (f_one B))
   have hf:= hr.bound
   rw [he] at hf
   have hv' := (Brush.certified (x:=x) (k:=B.order) zero_le_one (-(W 1-M))).climb (le_trans (by rw [norm_neg]) hf) le_rfl
   apply ((h' x hv hZ).gathering hv').climb (by push_cast; linarith) le_rfl |>.shimmy
   filter_upwards with i; change W _-W 1= (W _ - M) + -(W 1-M); ring
end cards
end YM.RG01Estimate.Promise
