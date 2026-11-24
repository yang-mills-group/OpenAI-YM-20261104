import YM.FVAAlt2.Rocket.Scale
/-! # At these history prices our relative soft discrepancy is further promoted
 with the actual input. R:μ top-only, cover `
 kickStart` chosen prior to any probe and s₂ vacuum charge.
 Absorb polynomial$\mathscr L$ enlargement ensuring combined soft error buys MANY powers of
 ε^{-1}. This scheme can multiply bare-to-MS before X normalization; important
 if you wanted to substitute this actual raw periodic computation for the upright
 solution without switching bare stencils. (`Z.main` in these theorems **infinite cover** as always.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain RegulatorIR.Profiles Sources Labels Source Momentum
open Oracle Atlas Epoch Calibration Kick YM.FVAAlt2 Billing
open MS MS.Menus MS.Dial MS.Land
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u b p r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ c₀:ℝ}(F:Calibration.Tent M){x:X→Room}{L:Meter X}
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable {Λ:Frames G}{H:Hol G} (R:Lobby.Registry Λ H)[LinearOrder I] [Fintype I]
variable (J:Choice M)
variable {D:Precision.ChartRatio G} (hD:Precision.LocalRatio D) (hq:Atlas.SatisfiesQ G Y S Z B p u γ) (hver: Calibration.Notebook S Y G Z g (native M) F p) (hc:∀ w,B.peak (Page.opening M w)=0) (hP:∀ w,S.l (Page.opening M w)=1)
variable (hL:OfAge B L)(hN: ∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v) (hg:G.Simple) (hb:quantum 1 0 ≤u)(hp:0<c₀)(ht:(S.dialect Y G Z (sheet F)).cushion c₀ x)
variable {d: MS.Local.Physical.Deck G} (l:I→ Rake.Label d)(z:X→I→ Cover)
set_option quotPrecheck false
local notation "PS"=> PowerSeries ℂ
local notation "w'"=> wage S Y Z F J γ
local notation "ƛ"=> stopped S Y Z F R
local notation "ℏ"=> fun i:I=>(l i).h
local notation "U_" i:max=> (Λ.level (ℏ i)).Index
local notation "V_" i:max=> Glyph d (ℏ i)
set_option quotPrecheck false
-- unscaled. still at native length
local notation:max "n_" w:max => n P_ w
def soothed (w:X): PS:= ∑ v:((i:I)→ Lobby.JLit Λ (l i)), C (∏ j: I,Lobby.γ R (l j) (v j)) * (PowerSeries.mk (fun e=> Complex.ofReal (ƛ univ ℏ v J z w e)))
variable (T:MS.Land.Prescription d) (θ:X→ℝ)
-- pay prices on calling stage BEFORE Λ estimator. Distinct evaluation mounts.
def billable (w:X): PS:= ∑ v:(i:I)→ V_ i, (∏ k,bore l T (θ w) k (v k))* (Lobby.redo T.team (θ w) (soothed S Y Z F R J (fun i=> Lobby.owner (v i)) z w))
variable (ε:X→ℝ)
def adjust (w:X): PS:= C ((ε w:ℂ)⁻¹ ^ Lobby.wt l) * billable S Y Z F R J l z T θ w
local notation:max "f_" w:max => wrap (n_ w) ∘ z w
variable (hz:∀ i,Nearest x L fun w=>z w i)(ha:∃ y,Nearest x L y)
variable (hθ:Poly L fun i=> ‖θ i‖ₑ)(hε:Poly L fun i=> ‖(ε i)⁻¹‖ₑ)
include hD hq hP hc hver hL hN hg hp hb ht hz ha
lemma soothing : Scored L w' p fun w=> Lobby.WilsonPoint D R _ (f_ w) l - soothed S Y Z F R J l z w:=by
 unfold Lobby.WilsonPoint soothed; simp_rw [← Finset.sum_sub_distrib,← mul_sub]; refine Scored.sum _ _ (fun i _=>?_) -- hidden defeq function family
 refine Scored.mul (V:=fun _=> C (∏ k:I,Lobby.γ R (l k) (i k))) (fun e _=> Poly.standard _ (by finiteness)) (hp:= ?_) -- maybe named issue
 intro e he; simp_rw [map_sub,Lobby.ΦbaseT, PowerSeries.coeff_mk];
 apply (soothe S Y Z F R univ ℏ i J hD hq hver hc hP hL hN hg hb hp ht z (fun i _=> hz i) ha e he).mono; intro w; dsimp only; rw [← Complex.ofReal_sub]; simp_rw [←ofReal_norm,Complex.norm_real]; exact le_rfl
include hθ
lemma subsidized : Scored L w' p fun w=> Lobby.prepare D R T (θ w) l _ (f_ w)- billable S Y Z F R J l z T θ w:=by
 unfold Lobby.prepare billable; simp_rw [← Finset.sum_sub_distrib,← mul_sub,← map_sub]; refine Scored.sum _ _ (fun k _=> ?_); exact Scored.mul (Price.prod univ _ (fun j _=> chargeGlyph T hθ l j (k j))) ((soothing S Y Z F R J hD hq hver hc hP hL hN hg hb hp ht (fun j=> Lobby.owner (k j)) z hz ha).reset T hθ)
include hε
lemma funded (h:∀ i,ε i≠0) : Scored L w' p fun w=> Lobby.newEra D R T (θ w) l (f_ w) (ε w) - adjust S Y Z F R J l z T θ ε w:=by
    simp_rw [fun w=> Lobby.tot_cost D R T (θ w) l (f_ w) _ (h w),adjust,← mul_sub]
    apply Scored.mul ?_ (subsidized S Y Z F R J hD hq hver hc hP hL hN hg hb hp ht l z T θ hz ha hθ)
    apply Price.C'; simp_rw [← Complex.ofReal_inv,← Complex.ofReal_pow]; exact complexView (powerLaw hε _)
end YM.RegulatorIR.FVAAlt2.Rocket
