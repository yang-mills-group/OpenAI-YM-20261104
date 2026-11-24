import YM.AllOrder.Fire.Logic
/-!
# Connected heat calculus for normalized tilted Gaussian cumulants

Instead of individually charging disconnected contractions in a subtractive
identity, use a true finite-order graded heat equation; at least one
new differentiation pair at every product. `equateF`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
local notation "Ω"=>X×Y
local notation "T"=>ℝ×(X×Y)
open GaussianScore
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] (A: Law Y)
    {ι:Type} [Fintype ι] (B:Basis ι ℝ Y) [MeasurableSpace Y][BorelSpace Y] (μ: Measure Y) [μ.IsAddHaarMeasure]
local infix:65 " #+ " => alters
variable {u : Book (X × Y)}
abbrev moment (g: T):=g.1
def plate (u: Book (X × Y)) (k:ℕ): T→ℝ:= Hot A μ (EXP u k)
def Warm (u:Book (X × Y)):Book (ℝ × (X×Y)):= LOG (plate A μ u)
local notation "W"=>Warm A μ u
local notation "A₀"=>plate A μ u
local notation "e"=>fun i=>foot (vec (X:=X) B i)
local notation "f"=>fun i=>foot ((0:X),Inv A B i)
local notation "g₀"=>((1:ℝ),(0:Ω))
lemma fix0 (h:u 0=0) (κ:T):plate A μ u 0 κ=1:= by unfold plate; rw [wins h]; exact average_const ..
lemma eventA (hf:Clear u)(h:u 0=0):Clear (Warm A μ u):= log_p (u:=plate A μ u) (fun _i=> flavor (exp_p hf h _) ..) (funext (fun x=>fix0 A μ h x))
def fronds (v: Book (ℝ×(X×Y))): Book T:= ∑ i : ι, ((slope ((f) i) v #+ slope ((e) i) v)+ slope ((f) i) (slope ((e) i) v))
-- curvature column Laplace plus at least one cross contraction in first part
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma spring [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]  (v:Book T) : ∀ i p, (wirings (moment) #+ v) i p=p.1*v i p:= fun i p=> congr_fun (exact_scale p.1 (Function.swap v p)) i
omit [FiniteDimensional ℝ X] [MeasurableSpace Y] [BorelSpace Y] in
lemma sorted [FiniteDimensional ℝ X] [MeasurableSpace Y] [BorelSpace Y]  (v:Book T) (i : ℕ) : (∑ j:ι, slope ((f) j) (slope ((e) j) v)) i=lap A B (v i):= by rw [Finset.sum_apply]; rfl
include B
lemma springboard (h:u 0=0) (hf:Clear u) : wirings moment #+ (∑ j:ι,slope ((f) j) (slope ((e) j) A₀))=slope g₀ A₀ := by funext i p; rw [spring,sorted]; exact (lightning A B μ p (exp_p hf h _)).symm
lemma equateF (h:u 0=0)(hf:Clear u): slope g₀ (Warm A μ u) = wirings moment #+ fronds A B W:= by
   let L:= plate A μ u; let g:=W; let T':= fronds A B W; have hg : L 0=1:=funext fun i=> fix0 A μ h i; have hh: W 0=0:=fades hg; have hw :Clear W:= eventA A μ hf h; have hF: Clear L:= fun i=> flavor (exp_p hf h _) ..
   have he: EXP g= L:= exponent_inv hg
   have hs (x:T): slope x L=L #+ slope x g:= he ▸ charges_log x hw hh
   have hx : ∑ j:ι, slope ((f) j) (slope ((e) j) L)= L #+ T':= by
      unfold T' fronds; rw [alt_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [hs,combine _ hF (hw.step _),hs, alt_add,associate]
   have hm:= springboard A B μ h hf; change wirings moment #+ _ = slope g₀ L at hm
   apply colI (u:=L) (fun i=> (congr_fun hg i).trans_ne one_ne_zero); change L #+ slope _ g = L #+ (wirings moment #+ T'); rw [← hs,←hm, show ∑ i:ι,slope ((f) i) (slope ((e) i) A₀)= _ from hx, ← associate, commute (wirings moment) L, associate]
end YM.AllOrder.Fire
