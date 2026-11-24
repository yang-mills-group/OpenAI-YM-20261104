import YM.FVAAlt2.Rocket.Fuel
import YM.FVAAlt2.Top
/-! # Heading to Scale comparison, prephysical (i.e. in the coordinates of a chosen MS_Data)
- uses the exact `LPT_to_MS` implementation with Pl extension (which coincides
  via Frame with Board.W.Y).
- actual microscopic program $
 L,F$, in the **RegulatorIR** calculus. Real analytic limits from YM phase not herein.
- through finite order p at every lattice spacing. All budgets named; this tour SERVES
  a trial but does not claim existence of needed geometry or how it was selected from
  actual budgets. `Admission` reqs. (See next modules.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Topology Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain RegulatorIR.Profiles Sources Labels Source Momentum
open Oracle Atlas Epoch Calibration Kick YM.FVAAlt2
open MS MS.Menus MS.Dial MS.Land MS.Vista MS.Fleet MS.Tide MS.Orbit MS.High MS.Port
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u a b p r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ c₀:ℝ}(F: Calibration.Tent M){x:X→Room}{L:Meter X}
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable (J:Choice M)[LinearOrder I][Fintype I]
variable {Λ:Frames G}{H:Hol G} (R:Lobby.Registry Λ H) (T:MS.Dial.Trial X I)(μ:ℝ){Ξ:MS.Local.Physical.Deck G}(c:I→ Rake.Label Ξ)(K₁:MS.Land.Prescription Ξ)
local notation:max "Θ" i:max=> T.profile.θ i
set_option quotPrecheck false
local notation "Θ'"=> T.profile.θ
local notation "ε'"=> fun i=> Real.exp (- Θ i )
abbrev Zpose (T:MS.Dial.Trial X I) (i:X) (w:I):Cover:= T.head i+ T.off w i
abbrev interpreted (v:ℕ)(i:X): ℂ := coeff v (adjust S Y Z F R J c (Zpose T) K₁ (fun i=> μ-Θ i) ε' i)
local notation "∂'"=> interpreted S Y Z F J R T μ c K₁
variable (hq:Atlas.SatisfiesQ G Y S Z B p u γ)(hver: Calibration.Notebook S Y G Z g (native M) F p) (hc:∀ w,B.peak (Page.opening M w)=0) (hP:∀ w,S.l (Page.opening M w)=1)
variable {D:Precision.ChartRatio G}(hD:Precision.LocalRatio D)(hL:OfAge B L)(hN:∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v)(hg:G.Simple) (hb:quantum 1 0 ≤u)(hp:0<c₀)(ht:(S.dialect Y G Z (sheet F)).cushion c₀ x)
variable (l:Filter X)(h:Pace S J T.profile.θ l L) (Hn: n ∘ Page.opening M= MS.Orbit.dimT T.side) -- can't notation in variable type
variable (h₀:∃ y,Nearest x L y)(hτ:∀ i,Nearest x L fun w=> Zpose T w i)
include hq hver hc hP hD hL hN hg hb hp ht h Hn h₀ hτ
lemma elected (he:r≤p)(q:ℝ)(hh:0<q): PeakT l T.profile q (∂' r-Lobby.evaluateR D R K₁ c T μ r):=by
    have hm: Scored L (wage S Y Z F J γ) p (fun w=> Lobby.newEra D R K₁ (μ-Θ w) c (wrap (n (P_ w)) ∘ Zpose T w) (ε' w)-adjust S Y Z F R J c (Zpose T) K₁ (fun i=> μ-Θ i) ε' w):= by
       apply funded S Y Z F R J hD hq hver hc hP hL hN hg hb hp ht c (Zpose T) K₁ (fun i=>μ-Θ i) ε' hτ h₀ ?_ ?_ (fun i=>(Real.exp_pos _).ne')
       · have hz(w): ‖Θ w‖≤ ‖Real.exp (Θ w)‖:= by rw [Real.norm_of_nonneg (T.profile.room w),Real.norm_of_nonneg (Real.exp_pos _).le]; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
         exact polySub ( Poly.standard L (by finiteness:‖μ‖ₑ≠⊤) ) (h.account.mono fun w=> by simp_rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hz w))
       simp_rw [Real.exp_neg, inv_inv]; exact h.account
    have hi := hm r he
    apply paceρ S Y Z F h hq.θ_pos hq.θ_low (hi.mono ?_) hP q hh
    intro w; dsimp only; rw [map_sub,Pi.sub_apply, enorm_sub_rev,Lobby.evaluateR]; unfold Lobby.situated; rw [show (MS.Orbit.dimT T.side w)=n (P_ w) from (congr_fun Hn w).symm]; exact le_rfl
variable {A:Booked Ξ}(U:MS_Data G A)(hK:TaylorOKPl U (Lobby.Table R Ξ) K₁) (hT:Dial.Uses T l μ)
include hT hK
lemma final_stage (he:r≤p): PeakT.twin l T.profile mildG (∂' r) (fun i=> Dial.tour U c μ (testP T i) Finset.univ r):=by
    obtain ⟨H,H'⟩:= (Lobby.pays_all D R K₁ c U hD hT hg hK).pay r
    refine ⟨H,?_⟩
    have hx:= PeakT.plus (elected S Y Z F J R T μ c K₁ hq hver hc hP hD hL hN hg hb hp ht l h Hn h₀ hτ he mildG mild_p) H'
    rwa [sub_add_sub_cancel ..] at hx
end YM.RegulatorIR.FVAAlt2.Rocket
