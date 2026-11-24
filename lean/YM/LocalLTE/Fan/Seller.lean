import YM.LocalLTE.Fan.Lucent
/-! Concrete stencil x in live Root f. Interaction assembly. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (H:Cash W t μ L Q o a T R)(K:Captain H j C v z r Y C' w B q m χ)
variable {p:ℕ} (D:Slots p→ Finset (Veil c f))(V:Tuple H.ThinP p)
section serial
open Tensor
-- Cone convert stem only needed in sunny probes. Reanchor via x chart fold costs supplied.
local notation "SC"=> Disk G c
local notation "EC"=> Directions G c
variable (n)
-- composition with x↦ (constant, CLM x) still polynomial. use iterated.
lemma curveL {E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F] [NormedSpace ℝ E][NormedSpace ℝ F] {f:E→ℝ}(p:Cabana.Pkt F n)(x:F)(L:E→L[ℝ] F)(hf:f=fun y=> Cabana.actual p (L y+x))(i:E) : ContDiffAt ℝ (↑n) f i ∧ iteratedFDeriv ℝ n f i=0:=by
  subst f; let P z:=Cabana.actual p (z+x); have hx:ContDiff ℝ ω P:= (Cabana.moves _ ω).comp (contDiff_id.add contDiff_const)
  refine ⟨((hx.comp L.contDiff).contDiffAt.of_le le_top),?_⟩
-- apply coeff
  change iteratedFDeriv ℝ n (P ∘ L) i = _; rw [Blaze.linear_pull L (hx.of_le le_top |>.contDiffAt)]; unfold P; rw [iteratedFDeriv_comp_add_right, Cabana.highPoly p (L i+x) (le_refl n)]; rfl -- edit

def speedΛ (U:Tuple H.ThinP p):=Ursell.coefficient H.seam U/(p+1).factorial
-- canonical amounts from W address geometry.
def flyer (n k:ℕ)(w:ℕ→ℕ)(L:Directions G c→L[ℝ] Directions G c)(χ:Chi)(z: Directions G c):= speedΛ H V *forecast H D n k w χ (gStep R.beta,L z)
def owner (n k:ℕ)(w:ℕ→ℕ)(L: Directions G c→L[ℝ] Directions G c)(χ:Chi): Cabana.Pkt (Directions G c) (pie n+1):=fun i=> Tensor.coeff (flyer H D V n k w L χ) i.val 0
-- complete rep. stem=T.w experiences.
lemma lives (n k:ℕ)(w:ℕ→ℕ)(L:Directions G c→L[ℝ] Directions G c)(χ:Chi): Cabana.actual (owner H D V n k w L χ)=flyer H D V n k w L χ:=by
  let p₀:=pie n+1; let g:=Field.forecast H D n k w χ; let f:= flyer H D V n k w L χ; let h' (x:EC):=g (gStep R.beta,L x); let x':SC:=(gStep R.beta,0); let K:= Cabana.actual (owner H D V n k w L χ)
  let A:EC→L[ℝ] SC:= (0:EC→L[ℝ] ℝ).prod L
  let X:= fun i: Fin p₀ => Tensor.coeff (fun x=> rune H D x k w χ n) i.val 0
  have hx:g= Cabana.actual X:= by unfold Cabana.actual X g forecast LocalLTE.stem; exact (Fin.sum_univ_eq_sum_range (fun i:ℕ=> Tensor.diagonal (Tensor.coeff _ i 0)) p₀).symm
  have hh : h'=fun y:EC=> Cabana.actual X (A y+x'):=by
    funext j; unfold h'; rw [hx]; refine congr_arg (Cabana.actual X) ?_; apply Prod.ext
    · exact (zero_add _).symm
    exact (add_zero _).symm
  have he : f=speedΛ H V • h':= rfl; have hp:K= LocalLTE.stem p₀ f := by unfold LocalLTE.stem K Cabana.actual owner; exact Fin.sum_univ_eq_sum_range (fun i:ℕ=> Tensor.diagonal (Tensor.coeff f i 0)) p₀
  have hf (x:EC) : ContDiffAt ℝ (↑p₀) f x ∧ iteratedFDeriv ℝ p₀ f x=0 := by rw [he]; obtain ⟨h1,h2⟩:= curveL p₀ X _ A hh x; refine ⟨h1.const_smul (speedΛ H V),?_⟩; rw [iteratedFDeriv_const_smul_apply h1,h2,smul_zero]
  have hz : f =ᶠ[𝓝 (0:EC)] K:= by
    filter_upwards [ball_mem_nhds (0:EC) zero_lt_one] with x hx
    have hh:= LocalLTE.pays (j:=p₀) (n:=p₀) zero_lt_one le_rfl (le_refl (0:ℝ)) le_rfl (fun x _=> (hf x).1) (fun x hx j h₁ h₂=>by obtain rfl:= le_antisymm h₂ h₁; unfold normJ; change ‖iteratedFDeriv ℝ p₀ f x‖ ≤_; rw [(hf x).2,norm_zero]) x hx
    have ht:=hh.bound; rw [← hp] at ht; exact sub_eq_zero.mp (norm_le_zero_iff.mp (by rwa [zero_mul] at ht))
  apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜:=ℝ) (fun x _=> ?_) (fun x _=> ?_) hz.symm
  · exact ((Cabana.moves _ ω).contDiffAt).analyticAt
  rw [he]; refine (show ContDiff ℝ ω (fun y=>speedΛ H V • h' y) from (ContDiff.const_smul (speedΛ H V) (f:=h') ?_)).contDiffAt.analyticAt; rw [hh]; apply (Cabana.moves _ ω).comp; exact A.contDiff.add contDiff_const
end serial
end YM.LocalLTE.Fan.Field
