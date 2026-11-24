import YM.RG12.Orifice.Cond
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Palmate
import YM.RG12.Spins.Tubal
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Orifice.CashCond
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Gate Scroll Vine Tablet Metric Pulse Itinerary
variable {x Y W η r Q:ℝ} {n j:ℕ}
-- simpler: analytic.Ray full Gauge rotation.P.Content only when seeds empty.Body. no uniform coerc claim.
open Source WardBin.Lies Set
-- law.Post. only requires Port at (vary X (U x)), which is good horizontal at those requests. exposes velocity in rhs (adapted from mistropy). use also unscaled in `militia` for origin zerofderiv
lemma rooms12 (P : Teller G)(L:Side)(D:Patch)(hd:D.Branches P.bind G)(j:ℕ){η r Q:ℝ}(Y:ℝ)(ho:Torch η r Q) {a:ℝ}(V:ℝ→ℝ) (he:Rate G L a V):
    ∃ K d : ℝ→ℝ,Rate G L 0 K∧ Rate G L a d ∧ ∀ x : ℝ,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F: Forest S.ratio)(X:Coat T F)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E → Config G c)(y:E), S.patch=D→ S.patch.L=L→X.x=x → Port P L η r Q Y (vary X (U y)) → Mode U y j (V x) →∀ i:Bond f, Brush j (K x) (d x) (film X i ∘ U) y:=by
  obtain ⟨C,hC,H⟩:= bounded_stencils P D hd
  let t := P.top.width; let b:= min (t/2) (retain η r Q)
  have hv : 0 < b := lt_min (half_pos P.top.width_pos) ho.prices
  have ht : b<t := (min_le_left ..).trans_lt (by have hx : 0 < t:=P.top.width_pos; linarith)
  let A := carat D P L b C; let R:= A*A+1; let f (x:ℝ):= kernelGrowth (radiusB x) G (V x); let m:= tubularPrice G L
  let u (x:ℝ):= (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η r Q m)+crownP j (radiusB x) m G η r Q R
  let v (x:ℝ):= f x+f x; let Z x:= v x+driftP j (v x)
  have hF : Rate G L a Z := (jet_growth G L he|>.add (jet_growth G L he)).add (((jet_growth G L he).add
    (jet_growth G L he)).mul_left _)
  have he : Rate G L 0 u := (Rate.const _).add (((polynomial G L j m _ _).mul_left _).mul_left (Fintype.card G.ColorIndex))
  refine ⟨u,Z,he,hF,?_⟩
  intro x c f' S T F X E _ _ _ U y hS hL hX hp hu i
  subst x; let Y':= vary X (U y); let D:= X.shutter
  have hf := hp.sails.room
  have hP := plates X _ hS hL hf hu _ hC (H _ _ S T hS hf.accepted) hv.le ht
  have hh:= plotsB D (x:=y) (fun v=> (vary X (U v)).plate) hp.sails.scale hP (show b≤retain η r Q from min_le_right ..) ho i
  let p₀ := Pulse.Batch.joint X.blank.plate D i
  have hK : ‖p₀‖ ≤ (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η r Q m) := Pulse.Batch.nearBase D ho (show Allow X.blank.plate (along S) m η r Q from hp.empty.scale) i
  exact semi (((Brush.certified hh.pos p₀).climb hK le_rfl).separating hh)

-- first analytic port.Need healthy T=1. Universe rolling.Any Mode.
lemma militia (hG:G.Simple)(P : Teller G)(L:Side)(D:Patch)(hd:D.Branches P.bind G)(j:ℕ){η r Q:ℝ}(Y:ℝ)(ho:Torch η r Q)
    (V : ℝ→ℝ) (hv : Rate G L (-(1/2)) V){W:ℝ} : ∃ K:ℝ→ℝ, Rate G L (-1) K ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio)(X:Coat T F)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E→ Config G c)(y:E), S.patch=D → S.patch.L=L → X.x=x → X.width=W → X.seeds=X.blank.seeds → Tent P L x W η r Q Y T → Mode U y j (V x) → U y=1 → ∀ i:Bond f, Brush j (|K x|) 1 (film X i ∘ U) y:=by
   obtain ⟨D₁,d1,h₁,h1,hx⟩ :=rooms12 P L D hd j Y ho V hv
   have hw:=h1.below (by norm_num) 1 zero_lt_one
   refine ⟨fun x=> D₁ x * d1 x^2,?_ ,?_⟩
   · convert! h₁.mul (h1.pow 2) using 1; norm_num
   filter_upwards [hw,eventually_gt_atTop (1:ℝ)] with x hw hp c f S T F X E _ _ _ U y hS hL hX hW hE ht hu hU i
   have hβ:0 < Pressure.temp x := Work.E09.temp_pos (zero_lt_one.trans hp)
   have hl: (vary X (1:Config G c)).manifest:=by
      unfold Coat.manifest vary; dsimp only; rw [hE,hX]; change (∅:Support c)=_; apply Eq.symm; ext a; simp only [Finset.notMem_empty,iff_false]; intro hk
      exact Finset.disjoint_left.mp (Next.Foundations.one_healthy (G:=G) ({a}:Support c) (Pressure.temp x) hβ.le) (mem_singleton_self _) hk
   have hQ:=ht F (vary X (1:Config G c)) hX hW hl
   obtain ⟨w,hh⟩:=pose (G:=G) c 1; obtain ⟨D,d,_,_,hP⟩:=rooms12 P L D hd 1 Y ho (fun _ :ℝ => w) (Rate.const w)
   have h:= Work.G07.at_zero_increment (1:Config G c)
   set F' := film X i ∘ U
   have hD:DifferentiableAt ℝ (film X i ∘ increment (1:Config G c)) 0:= ((hP _ _ _ S T F X (Directions G c) (increment 1) 0 hS hL hX (h.symm ▸ hQ) hh i).smooth).differentiableAt one_ne_zero -- hf 1 type
   have he : F' y=0:= by change film X i (U y)=0; rw [hU,← h]; exact (route0 X hE hX hW hG ht hβ i hD hh (le_refl _) h).1 -- this returns W=1 at incr.W. Need U.h.U. rw
   have hP:= hx x _ _ S T F X E U y hS hL hX (hU.symm ▸ hQ) hu i
   have hw:= (le_abs_self _).trans hw
   refine ⟨hP.smooth,zero_le_one,?_⟩; rintro (_|_|k) hk
   · unfold normJ; rw [norm_iteratedFDeriv_zero,he,norm_zero]; positivity
   · change ‖iteratedFDeriv ℝ 1 F' y‖≤ _; rw [norm_iteratedFDeriv_one,show fderiv ℝ F' y = 0 from (route0 X hE hX hW hG ht hβ i hD hu hk hU).2,norm_zero]; positivity
   exact (hP.order _ hk).trans (le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hP.pos hw (show 2 ≤ k+2 by omega)) hP.nonneg) (by simpa only [one_pow,mul_one] using (le_abs_self (D₁ x*d1 x^2))))
end YM.RG12.Orifice.CashCond
