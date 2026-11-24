import YM.AllOrder.Floe.Fly
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent PriceCompiler
namespace PlanV
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D:RG.Supply.Rolls X.p}(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) -- x stage fine from D
local notation "B" => X.K
local notation "A" => X.p.profile
local notation "p" => X.p.profile x
local notation "q" => X.p.profile y
local notation "K" => X.p.kernel
local notation "O"=> X.O
local notation "Ωz" => abs (X.K.Ω x)
local notation "Ωy" => abs (X.K.Ω y)
variable (D) (hx:4≤x)
set_option quotPrecheck false
local notation "P" => Mural.sheet X.p D hx
local notation "C₀" => Pane.cloak D x
local notation "P'" => Plateau.Ticket (P) K O (A x) (A y) (Pane.cloak D x)
local notation "s₁" => R.pre k x
local notation "s₂" => R.pre k y
local notation "T" => tape (k+2)
local notation "I"=> Card D R x y hx k
-- audit arg x implicit λ.
local notation "X0" => fun i:I=> Card.extra i
local notation "V₁" => (p).clip
local notation "V₂" => (q).clip
local notation "Q"=>Plateau.Art (G:=G) (N:=k+2) P K (A x)
-- use notation projections via `₁(x)`
local notation "M₁" => (fun i:I=> i.self.north)
local notation "M₂" => (fun i:I=> i.self.south)
local notation "Λ₀" => (fun i:I=> i.self.paid)
local notation "α₀" => (fun i:I=> i.self.alpha)
local notation "hU" => (fun i:I=> i.self.upCost)
local notation "f₀" => (fun (j:Age)(i:I)=> authority k j i.self.paid)
/-! billing in φ. No shrinking horizon with β; same kernel chosen before any real leases.Fee uniform across steps. -/
open ConnectedActivityE6
abbrev strengthP (Λ:ℝ) := 2* mon Λ
lemma s_p (Λ:ℝ): 0<strengthP Λ:= mul_pos (by norm_num) (mon_pos Λ)
lemma deep_x : Tendsto strengthP atTop atTop:= mon_deep.const_mul_atTop (by norm_num)
abbrev budget (o:ℕ)(Λ:ℝ):ℝ:= (1+|Λ|)^o
abbrev Ψ (Λ:ℝ) := 1+|Λ|
lemma beyond : Tendsto Ψ atTop atTop:= tendsto_atTop_mono (f:=id) (fun x=>(le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) tendsto_id
lemma rate_x (G:Gauge)(L:Side): Tendsto (fun t:ℝ=> Ψ (strengthP (betaF G t L))/Ψ (strengthP t)) atTop (𝓝 1) := by
 have ht : Tendsto (fun t:ℝ=>1/strengthP t) atTop (𝓝 0):= tendsto_const_nhds.div_atTop deep_x; have hf : Tendsto (fun t:ℝ=> strengthP (betaF G t L)/strengthP t) atTop (𝓝 1):= (mon_ratio (G.slopeConstant*Real.log L.val)).congr fun i=> (by unfold strengthP; change PriceCompiler.mon _/PriceCompiler.mon i=_; rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠0)]; rfl);
 apply (show Tendsto (fun t=> ((1/strengthP t)+(strengthP (betaF G t L)/strengthP t))/(1/strengthP t+1)) atTop (𝓝 1) from (by convert! (Tendsto.div (ht.add hf) (ht.add_const 1) (by norm_num)) using 1; norm_num)).congr; intro t; unfold Ψ; rw [abs_of_pos (s_p t),abs_of_pos (s_p ..), ← add_div]; rw [show 1/strengthP t+1=(1+strengthP t)/strengthP t by rw [add_div,div_self (s_p t).ne']]; rw [div_div_div_cancel_right₀ (s_p t).ne' _ _]
lemma budget_ratio (G:Gauge)(L:Side) (o:ℕ): Tendsto (fun t:ℝ=> budget o (strengthP (betaF G t L))/budget o (strengthP t)) atTop (𝓝 1):=by simpa only [budget,Ψ, one_pow, div_pow] using (rate_x G L).pow o
namespace Income
variable (U:Income D R x y hx k)
-- constants depending Patch.J. Use at true Steps.Combines.S.Env.Quote inside Γ for any age, C cost theorem future.M.P. tighten δ law same order.
local notation "L" =>D.L x
local notation "Z₁"=> strengthP
local notation "Θ"=> fun (t:ℝ)=> Z₁ (betaF G t L)
local notation "w"=> fun t:Age=> R.wage x y k ((D.L x).val:ℝ) t
def Bears (t:ℝ) := ∀ i:I, i.self.paid=strengthP (betaF G t (L))→ ∀ j∈tape (k+2), Quoted (U.laid i j) (R.pre k y j) (authority k j (strengthP t)) ∧ (j.r=2→ |U.issue i j.e| ≤ authority k j (strengthP t))
lemma kindle(i:Age)(C:ℝ)(hp:0≤C): ∀ᶠ t:ℝ in atTop,C*budget (level k i) (Θ t)≤(1/4:ℝ)*authority k i (Θ t):= by
 filter_upwards [((beyond.comp (deep_x.comp (Work.E09.betaF_growth G (D.L x)))).eventually_ge_atTop (4*C))] with i' he; change 4*C≤ Ψ (Θ i') at he; let b:= Ψ (Θ i'); let o:=level k i; have hz:0≤b:= zero_le_one.trans (one_face _) -- syntax.. change
 change _*b^o≤_*b^(o+1); rw [pow_succ]; nlinarith only [he, mul_le_mul_of_nonneg_right (show 4*C ≤ b from he) (show 0 ≤ b^o from pow_nonneg hz _)]
include U
variable (hL: R.Rise x ((D.L x).val:ℝ))(hY:k+2≤ y)(he:StepStages x y)
include hL hY he
lemma bearing : ∀ᶠ t:ℝ in atTop,Bears D R x y hx U t:= by
 let A' i t:= authority k i (strengthP t); let T'(i:Age)(t:ℝ):=∀ j:I, j.self.paid=Θ t→ Quoted (U.laid j i) (s₂ i) (A' i t)∧ (i.r=2→ |U.issue j i.e|≤ A' i t);
 have hv (i: Age) (hi:i∈T) :∀ᶠ t:ℝ in atTop, T' i t:= by
     let hT:= U.sustenance; obtain ⟨f,⟨C,h,hF⟩,hv⟩:=hT.rents i hi; let d:=level k i; have hl: ∀ᶠ t:ℝ in atTop, Ψ (Θ t)^(d+1) ≤ 2*A' i t:= by filter_upwards [(budget_ratio G L (d+1)|>.eventually (ge_mem_nhds (one_lt_two)))] with i ht; exact (div_le_iff₀ (pow_pos (by unfold Ψ; positivity) _ : 0< Ψ (Z₁ i)^(d+1))).mp ht
     have hm :∀ᶠ t:ℝ in atTop,∀ j:I,j.self.paid=Θ t→ Quoted (U.laid j i) (s₂ i) (A' i t):= by
        filter_upwards [kindle (k:=k) D x i C h,hl] with t hζ hl j hq; have he':= (hL y he k hY i hi).rent; apply (hv j).narrow le_rfl; let ξ:=A' i t; let z:=authority k i (Θ t); change w i*authority k i j.self.paid+f j≤ ξ; have hf:f j≤ (1/4:ℝ)*z:= ((hF j).2.trans (by change C*budget d j.self.paid≤_; rw [hq]; exact hζ)); rw [hq]; change _*z+_≤_; nlinarith only [hf,mul_le_mul_of_nonneg_right he' (show 0 ≤ z from pow_nonneg (by positivity) _),show z ≤ 2*ξ from hl]
     by_cases hx':i.r=2; swap; · exact hm.mono fun t ht j hg=>⟨ht j hg,fun hp=>(hx' hp).elim⟩
     have hi':i=bottom i.grade:= by rcases i with ⟨i,v,h⟩; have hv:v=0:=Nat.add_right_cancel hx'; subst v; rfl
     obtain ⟨q',ht',hη⟩:= (show CreditF (Λ₀) d (fun j=> |U.issue j i.e|) from (by have hk:i.grade<k:= (show i.grade<k from by have he:=Age.in_scope.mp hi; unfold Age.e at he; omega); nth_rw 1 [show d=level k (bottom i.grade) from congr_arg (level k) hi']; exact U.sustenance.income i.grade hk)); filter_upwards [kindle (k:=k) D x i q' ht', hm,hl] with t hf h hζ j hk;
     refine ⟨h j hk, fun _=> (hη j).2.trans (le_trans (b:=1/4*authority k i (Θ t)) ?_ ?_)⟩; · exact ((show q'*budget d j.self.paid ≤ 1/4*authority k i (Θ t) from (by rw [hk]; exact hf)))
     unfold A'; have hh : 0 ≤ Ψ (Z₁ t)^(d+1) :=pow_nonneg (by unfold Ψ; positivity) _; linarith only [show authority k i (Θ t) ≤ _ from (show _ ≤ 2*authority k i (strengthP t) from hζ), show 0 ≤ authority k i (strengthP t) from hh] -- `filter` includes j hk! rewrite
 filter_upwards [(eventually_all_finset _ («p»:=T')).mpr hv] with t ht i he j h; exact ht j h i he
end Income
end PlanV
end YM.AllOrder.Floe.Step
