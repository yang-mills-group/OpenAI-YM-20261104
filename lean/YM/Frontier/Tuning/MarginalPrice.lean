import YM.Frontier.Tuning.AngularReceipt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Raisin
/-! Marginal angular quadratic charge, *on I only*. Polynomial of facescale reused at fixed
degree from Marginal/Flux, no sum of moments with cost growing on a full period here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.MarginalPrice
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option maxHeartbeats 1200000


lemma drafts (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {V u : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (hp : Rate G L (-(1/2)) u) (hv : ∀ᶠ x in atTop,0≤V x)
    {η r S' : ℝ} (Y : ℝ) (p:Torch η r S') (d : ℝ) : ∃ (k:ℕ) (B:ℝ→ℝ), Rate G L 0 B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ S.patch=D → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E→ Config G c) (F:Forest S.ratio) (X:Coat T F) (z:Air f G)
      (R:Rep G f), X.x=x → X.width=K → X.χ=χ → Port P L η r S' Y X → Intake P T x R → Mode U y j (V x) →
        Clutch X z a R.beta (|u x|) y j U (fun i=> steer X d (worldZ X R.beta z) (U i)) (fun i=>course X d R.beta z (U i)) →
          ∀ I, Brush j (|B x| * facescale I z^k) 1 (fun y=> draftI X I R.beta d (U y) z) y := by
  obtain ⟨A,R,hA,hR,hT⟩:= Blaze.vines P L D hD K γ W χ j p h hv 1
  obtain ⟨H,hH,hP⟩:= bounded_stencils P D hD
  let m:= carat D P L 0 H; let f:= m*m+1; let t:= tubularPrice G L; let g:=payE η r S' t
  let v x:= kernelGrowth (radiusB x) G (V x); let W' x:=driftP j (v x+v x); let b x:=facePrice j (radiusB x) t f g
  let B:=payE (retain η r S') (S'⁻¹/2) (1+g) t; let C x:= burst G L x * (|u x| + (|A x| +|A x|)); let F x y:= C x+y
  have hg:=(jet_growth G L h).weaken (b:=0) (by norm_num)
  have hd {V:ℝ→ℝ} (hA : Rate G L (-(1/2)) V):= hA.compare (v:=fun x=>|V x|) (Filter.Eventually.of_forall fun x=>(abs_abs _).le); have hc: Rate G L 0 C:= by unfold C;convert (burst_rate G L).mul ((hd hp).add ((hd hA).add (hd hA))) using 1 <;> first | rfl | ring
  have hf:=Polyprice.combine (Polyprice.fixed hc) (Polyprice.variableP G L)
  have ht : Polyprice G L (fun x _=>Tablet.token j (b x) B) := Polyprice.fixed (Flux.tokens G L (polynomial G L j t f g) j B)
  have hw' : Rate G L 0 W':=(hg.add hg).mul_left _; have hm := Polyprice.uniform G L 1; have hp' := Polyprice.fixed (show Rate G L 0 (fun x=>driftP j (W' x)) from hw'.mul_left (j:ℝ))
  let price x y:=y*(F x y*(Tablet.token j (b x) B * F x y))*(1+(1+(driftP j (W' x)+1)))^j
  obtain ⟨k,A',hA',hq⟩:=((Polyprice.variableP G L|>.together (hf.together (ht.together hf))).together ((hm.combine (hm.combine (hp'.combine hm))).powP j)).fees
  change ∀ x y:ℝ, 1≤y→|price x y|≤ |A' x| * y^k at hq
  refine ⟨k,A',hA',hT.mono ?_⟩
  intro x hx c f' S T hh hv hS E _ _ y U F' X z' A' he hK hχ h hv hM' hB' I
  have hΓ:= h.sails; have hX': X.manifest:= h.placed
  have hL:(vary X (U y)).manifest := hB'.tipped.symm ▸ hX'
  subst x
  have hc:Rotator P L η r S' Y (vary X (U y)) := by rw [hB'.tipped]; exact hΓ
  have hp := Gate.plates X D (by assumption) hh.length_eq hΓ.room hM' H hH (hP _ _ S T (by assumption) hh.funds) (le_refl 0) P.top.width_pos
  have hx' := hx c _ S T (by assumption) hh hS F' X E U y rfl hK hχ hM' hL hc.scale
  let p':= facescale I z';
  have hy:=hq X.x p' (Flux.expenses I z').1
  have hU : 0 ≤ F X.x p':=(add_nonneg (by unfold C; exact mul_nonneg (by unfold burst; positivity) (by positivity)) (zero_le_one.trans (Flux.expenses I z').1))
  have hs : (I.card*Fintype.card G.ColorIndex: ℕ) ≤ (p':ℝ):= by rw [show I.card*Fintype.card G.ColorIndex=(lensS I G).card by simp [lensS]]; exact (expenses I z').2.2.1
  refine (PhysicalNext.Repeat.Alabaster.orbitSum X I U (fun i=> steer X d (worldZ X A'.beta z') (U i)) hB' hc hp hx'.1 (abs_nonneg _) hU ?_H).climb (hy.trans' ?_K) le_rfl
  case _H=> apply add_le_add_left; apply mul_le_mul_of_nonneg_right (burst_h (L:=L) (hh.length_eq ▸ hv.window.2)) (by positivity)
  case _K=> have ht := Flux.feast X I U hc hp; have hB :0≤B:=(own_mat hc I).disc
            dsimp only [price]; apply le_trans _ (le_abs_self _); clear hy
            have hk' : 0≤ b X.x := by exact ht.basis
            have hv : 0≤ W' X.x := ht.pos
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (mul_nonneg hU (mul_nonneg (by unfold Tablet.token; exact sum_nonneg fun i _=> by change 0≤ (_*B+1)^_ *B; positivity) hU))) (pow_nonneg (by unfold driftP; positivity) _)
end YM.Frontier.Tuning.MarginalPrice
