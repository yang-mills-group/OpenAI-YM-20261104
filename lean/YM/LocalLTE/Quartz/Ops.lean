import YM.LocalLTE.Quartz.Speed
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
def twirled (m k:ℕ)(F:Directions G c→L[ℝ] Directions G c)(y: EC) := Field.speedΛ H z.2 * forecasts M φ H χ z D m k (gStep R.beta,F y)
def boat (m k:ℕ)(L:Directions G c→L[ℝ] Directions G c) : Cabana.Pkt (Directions G c) k:= fun i=> Tensor.coeff (twirled M φ H χ z D m k L) i.val 0
open Field
-- complete rep. stem=T.w experiences.
lemma aliveV (n k:ℕ)(L:Directions G c→L[ℝ] Directions G c): Cabana.actual (boat M φ H χ z D n k L)=twirled M φ H χ z D n k L:=by
  let p₀:=k; let g:=forecasts M φ H χ z D n k; let f:= twirled M φ H χ z D n k L; let h' (x:EC):=g (gStep R.beta,L x); let x':SC:=(gStep R.beta,0); let K:= Cabana.actual (boat M φ H χ z D n k L)
  let A:EC→L[ℝ] SC:= (0:EC→L[ℝ] ℝ).prod L
  let X:= fun i: Fin p₀ => Tensor.coeff (fun x=> mica M φ H χ z D n x) i.val 0
  have hx:g= Cabana.actual X:= by unfold Cabana.actual X g forecasts LocalLTE.stem; exact (Fin.sum_univ_eq_sum_range (fun i:ℕ=> Tensor.diagonal (Tensor.coeff _ i 0)) p₀).symm
  have hh : h'=fun y:EC=> Cabana.actual X (A y+x'):=by
    funext j; unfold h'; rw [hx]; refine congr_arg (Cabana.actual X) ?_; apply Prod.ext
    · exact (zero_add _).symm
    exact (add_zero _).symm
  have he : f=speedΛ H z.2 • h':= rfl; have hp:K= LocalLTE.stem p₀ f := by unfold LocalLTE.stem K Cabana.actual boat; exact Fin.sum_univ_eq_sum_range (fun i:ℕ=> Tensor.diagonal (Tensor.coeff f i 0)) p₀
  have hf (x:EC) : ContDiffAt ℝ (↑p₀) f x ∧ iteratedFDeriv ℝ p₀ f x=0 := by rw [he]; obtain ⟨h1,h2⟩:= curveL p₀ X _ A hh x; refine ⟨h1.const_smul (speedΛ H z.2),?_⟩; rw [iteratedFDeriv_const_smul_apply h1,h2,smul_zero]
  have hz : f =ᶠ[𝓝 (0:EC)] K:= by
    filter_upwards [ball_mem_nhds (0:EC) zero_lt_one] with x hx
    have hh:= LocalLTE.pays (j:=p₀) (n:=p₀) zero_lt_one le_rfl (le_refl (0:ℝ)) le_rfl (fun x _=> (hf x).1) (fun x hx j h₁ h₂=>by obtain rfl:= le_antisymm h₂ h₁; unfold normJ; change ‖iteratedFDeriv ℝ p₀ f x‖ ≤_; rw [(hf x).2,norm_zero]) x hx
    have ht:=hh.bound; rw [← hp] at ht; exact sub_eq_zero.mp (norm_le_zero_iff.mp (by rwa [zero_mul] at ht))
  apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜:=ℝ) (fun x _=> ?_) (fun x _=> ?_) hz.symm
  · exact ((Cabana.moves _ ω).contDiffAt).analyticAt
  rw [he]; refine (show ContDiff ℝ ω (fun y=>speedΛ H z.2 • h' y) from (ContDiff.const_smul (speedΛ H z.2) (f:=h') ?_)).contDiffAt.analyticAt; rw [hh]; apply (Cabana.moves _ ω).comp; exact A.contDiff.add contDiff_const
end YM.LocalLTE.Fan
