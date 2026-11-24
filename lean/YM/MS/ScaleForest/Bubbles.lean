import YM.MS.ScaleForest.LoadB
import YM.MS.ScaleForest.Entry
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionGhostPole

/-!
# Rank and scaling of the ghost-loop pole in AA (and setting up the total)

Use the angular_average of the same two-edge integral as for the
source-containing subgraph. Include colour. No separate normalization choice
for the ghost loop. Pole term in Lagrangian exponent has the quadratic half
when expressed as a product of fields; state it on repeated-derivative
symbols. Translated `z=-ε` these counterterms are negative residue over
ε in additive exponent conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.TwoPoint
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open Book Convolve Logarithm Signal Landau.Detect.Mark Arts Motif Halo Rock Path Oceans Plum Alps
open Garment Arc Spin Train Pearl Dock Shine GraphSum Hem Mell
open WilsonMS.BetaValue WilsonMS.BetaValue.HeatPapers SquareShift
open Complex (I)
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {m n : ℕ}

abbrev beamPair (G : Gauge) (σ : Bool) := firstSew (interaction G 1) (interaction G 1) (cursor σ)
abbrev stemPair (G : Gauge) (σ : Bool) := firstSymbol (interaction G 1) (interaction G 1) (cursor σ)
abbrev bubble (G : Gauge) (ξ σ : Bool) := GraphSum.loop (cursor ξ) (beamPair G σ)

def ratePair (G : Gauge) (ξ σ : Bool) (z : ℂ) : Mob G := closeG (cursor ξ).half z 0 (stemPair G σ)

def poleTensor (G : Gauge) (ξ σ : Bool) : Mob G := -highTensor 4 (ratePair G ξ σ) 0

variable (G) (ξ σ : Bool)

theorem poleK : (bubble G ξ σ).instructions.pole= Ice 1 (poleTensor G ξ σ) :=
  (twoVertex_laurent ..).2.1

theorem rank_pole : Cap0 true 0 (bubble G ξ σ).slots (fun _ : ℂ=> poleTensor G ξ σ) ∧ Home (poleTensor G ξ σ) 4 := by
  have ht : Lift (ratePair G ξ σ) (ratePair G ξ σ 0) :=
    (close_form (G:=G) (cursor ξ) ( firstResult (interaction G 1) (interaction G 1) (cursor σ))).2
  let H:= PoleVertex (bubble G ξ σ) 1 (poleK G ξ σ) (Lift.price (Lift.neg (high_lift ht 4)))
  exact ⟨H.cap,H.scaling⟩

theorem sum_pole (a b : CI G) (p : SectorP m) (i j : L m) :
    let V:= poleTensor G ξ σ; kinetic V a b p i j=tensor2 (along V a b) (across V a b) p i j:= by
  intro V; obtain ⟨hp,hX⟩:=rank_pole G ξ σ; have ht:= (sunny hp.fine.tune).exists.choose_spec
  exact summation_rule a b ht.token hX ht.price p i j

theorem stem_form (G : Gauge) (σ : Bool) : Form0 true (stemPair G σ) := by
  have H:= firstResult (interaction G 1) (interaction G 1) (cursor σ);
  exact collapsed_kernel (H ▸ (beamPair G σ).accepted.usable.clock : ClockD true 0 (beamPair G σ).slots _)

variable {G} (p q : QP) (mu : Axis) (a b : CI G)
local notation "Z" => word (m:=0) mu mu a b p

theorem inside_loop (w : Legs (Shore G 0)) :
    trc ((cursor ξ).half 0) q (stemPair G σ 0) w = ∫ r in (0:ℝ)..1, trc (Km 1 ξ 0) q (connective r σ G 0) w := by
    -- integral at unit upper length, linear- not log-length on first edge
    have hz : (cursor ξ).half= Km (G:=G) 1 ξ:= congr_arg (pickLine ξ) (radial_atOne G)
    rw [hz]
    have hu := (selected_radial σ (interaction G 1) (interaction G 1) 0).1
    let c:ℂ:= (factor true : ℂ); let U(l: Legs (Shore G 0))(r:ℝ):= connective r σ G 0 l
    have ht(l : Legs (Shore G 0)) : Continuous (U l) := continuous_const.mul (continuous_pick σ l (interaction G 1).symbol (interaction G 1).symbol)
    have hv(l : Legs (Shore G 0)): stemPair G σ 0 l=∫ r in (0:ℝ)..1,U l r:= by rw [posing,exp_zero] at hu; exact congr_fun (congr_fun hu 0) l
    simp_rw [at_trc,hv]; let f (a b:Cfield G 0)(t:ℝ):= Km 1 ξ 0 a b q * U ((a,q)::(b,-q)::w) t
    have He(a b): Continuous (f a b):= continuous_const.mul (ht _)
    rw [intervalIntegral.integral_finsetSum]; swap; · exact fun i _=> (continuous_finsetSum _ fun j _=> He i j).intervalIntegrable _ _
    refine Finset.sum_congr rfl fun i _=> ?_; rw [intervalIntegral.integral_finsetSum _]
    apply Finset.sum_congr rfl; intro j _; unfold U; rw [intervalIntegral.integral_const_mul]; exact fun j _=> (He i j).intervalIntegrable _ _

theorem log_rate : kinetic (ratePair G ξ σ 0) a b p (m:=0) mu mu= (∑ i:G.ColorIndex,angle i a b) *
    ∫ q:QP, (∫ r in (0:ℝ)..1, bothTensor r p q mu ξ σ+ bothTensor r p (-q) mu ξ σ) ∂mplane := by
  have hx := Path.lowN (stem_form G σ).price ((cursor ξ).ok.forms true).price (stem_form G σ).token
    ((cursor ξ).ok.forms true).token Z; push_cast at hx
  unfold kinetic ratePair; rw [closeG_eq,Pi.smul_apply,Pi.smul_apply,hx,fee_T0];
  rw [show (pitch 0:ℝ)=1 from (by simp [pitch]),one_smul]
  unfold Ccy; change _ = _; rw [smul_eq_mul, ← Complex.real_smul ];
  simp_rw [inside_loop,trace_value,intervalIntegral.integral_const_mul]
  rw [show mplane= ENNReal.ofReal room • (Px 0) from rfl, integral_smul_measure,
    ENNReal.toReal_ofReal room_pos.le, MeasureTheory.integral_const_mul,Complex.real_smul, Complex.real_smul, mul_left_comm]

theorem pole_slice : kinetic (poleTensor G ξ σ) a b p (m:=0) mu mu = (1/2:ℂ) *
    ( reading 2 (fun x:ℝ=> kinetic (ratePair G ξ σ 0) a b (x•p) (m:=0) mu mu )) := by
  unfold poleTensor highTensor kinetic; rw [ Pi.neg_apply, Pi.neg_apply, Pi.smul_apply,Pi.smul_apply,torch_equiv]; change -((_ : ℂ) * _)=_; ring

lemma cast_price (f : ℝ → ℝ) (h : ContDiff ℝ ∞ f) :
    reading n (fun x : ℝ => (f x:ℂ))= ↑((Nat.factorial n:ℝ)⁻¹* iteratedDeriv n f 0) := by
  have ht: iteratedDeriv n (fun x : ℝ => (f x:ℂ)) 0= ↑(iteratedDeriv n f 0) :=
    congr_arg (fun m : ℝ [×n]→L[ℝ] ℂ => m _) (Complex.ofRealCLM.iteratedFDeriv_comp_left
          (n:=∞) (x:=0) (f:=f) h.contDiffAt (by exact_mod_cast le_top))
  rw [reading,ht, Complex.real_smul]; push_cast; rfl

abbrev traceAd (a b : G.ColorIndex) := ∑ i:G.ColorIndex, angle i a b

theorem ghost_diag : kinetic (poleTensor G true true) a b p (m:=0) mu mu =
    traceAd a b * ↑(angularMoment p mu mu /12) := by
  have hp (p:QP) : kinetic (ratePair G true true 0) a b p (m:=0) mu mu = traceAd a b *
      (-8*(momentTensor p mu mu:ℂ)) := by
    rw [log_rate]; unfold bothTensor ghostTensor; simp only [ne_eq,not_true_eq_false,if_false,
      if_true,← mul_add];
    simp_rw [intervalIntegral.integral_const_mul]; rw [MeasureTheory.integral_const_mul,show (∫ q:QP,
        (∫ r in (0:ℝ)..1, twin p mu mu r q+twin p mu mu r (-q)) ∂mplane)=_ from (from_integral p mu mu).1]; unfold traceAd; ring
  rw [pole_slice]; simp_rw [hp,read_const,cast_price _ (moment_smooth ..), angular_average]; norm_num; ring

theorem crossed_pole (ht : ξ≠σ) (p : SectorP m) (i j : L m) : kinetic (poleTensor G ξ σ) a b p i j = 0 := by
  have he (p:QP) (mu:Axis) : kinetic (poleTensor G ξ σ) a b p (m:=0) mu mu=0:= by
    rw [pole_slice]; simp_rw [log_rate,bothTensor,if_pos ht]; simp [reading]
  rw [sum_pole]; simp [along,across,tensor2,he]

def counterScale : ℂ := ↑((logArea:ℝ)/12)

theorem dotProbe (mu:Axis) : primary 0 mu= kk mu 0:= by simp [primary,spray, Pi.single_apply,kk,show zeroDirection 0=(0:Axis) from rfl]

lemma primary_sq : (primary m).sq=1:= spray_price _

theorem along_gh : along (poleTensor G true true) a b = traceAd a b * (3*counterScale) := by
  change kinetic _ _ _ _ (m:=0) (0:Axis) (0:Axis) = _; rw [ghost_diag]; simp only [counterScale, angularMoment,
    dotProbe,kk_self]; rw [primary_sq (m:=0)]; push_cast; ring

theorem across_gh : across (poleTensor G true true) a b = traceAd a b * counterScale := by
  change kinetic _ _ _ _ (m:=0) (1:Axis) (1:Axis) = _; rw [ghost_diag]; simp only [counterScale,angularMoment,dotProbe,
    kk_self]; rw [primary_sq (m:=0),show kk 1 0=0 from if_neg (by decide)]; simp

def ghost_residue (x : SectorP m) (i j : L m) (c : ℂ) : ℂ :=
  c * counterScale * ((if i=j then (x.sq:ℂ) else 0) + (2:ℂ) * x i * x j)

theorem ghost_bill (p : SectorP m) (i j : L m) : kinetic (poleTensor G true true) a b p i j=ghost_residue p i j (traceAd a b) := by
  rw [sum_pole]; rw [along_gh,across_gh]; unfold ghost_residue tensor2; split_ifs <;> ring
end YM.MS.ScaleForest.TwoPoint
