import YM.MSbar.Mosaic.Around
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
local notation "λ'" i=> Cane.value (αm i) M.C M.A M.E M.s M.sway
-- Geometry.World.cost pieceB
variable (hR:∀ᶠ i in φ,Ore M (X i) K)
variable (P:Palisade){a b':ℝ}
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
include hX
lemma nearB (c:ℝ)(hv:0<c)(p:ℕ)(L:ℕ) : Van φ X (fun i=>Real.exp (-thorn (X i) p*spotN (X i))) ∧ Run φ X (fun i=> liftW (c*αm (X i)) p (L*closeN (X i))) 0:=by
    let w(i):= hatW (X i); let p'(i):= w i^(-3:ℤ); have hw:Tendsto w φ atTop:=Alto.broad.comp hX; let St(i):=thorn (X i) p -- typo
    let y(i):= radiusB (X i); have hy: Run φ X (fun i=>(y i:ℝ)) 0:= Run.Yceil hX (Run.stanza hX) (Eventually.of_forall fun i=>sq_nonneg _) -- ⌈W⌉
    let f(i):ℕ:=L*closeN (X i); have hf:Run φ X (fun i=>(f i:ℝ)) 0 := by unfold f closeN; push_cast; exact (hy.Ypow hX _).mulK hX _
    let g(i):= c*αm (X i)*(f i:ℝ); have hP(i): g i=c*p' i*(f i:ℝ):=rfl
    let v'(i):= Real.exp (g i); let B:=8*c*L; have hb: 0≤ B:=by unfold B; positivity
    have hk : Run φ X v' 0:=by
         refine (Run.token hX (Real.exp B)).cash ?_; filter_upwards [hw.eventually_ge_atTop 1] with i hi; have hu:0<w i:=zero_lt_one.trans_le hi; have hx:(y i:ℝ) ≤ 2*w i:=by
             have hv: (↑(y i):ℝ) < w i+1 := Nat.ceil_lt_add_one hu.le; linarith only [hv,hi]
         unfold v'; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; rw [hP]; have he:(f i:ℝ)≤ (L:ℝ)*(2*w i)^3:=by
             unfold f closeN; push_cast; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hx 3) (Nat.cast_nonneg _)
         unfold p'; rw [_root_.zpow_neg]; have hf':0 < (w i^ (3:ℤ))⁻¹:=by positivity
         refine (mul_le_mul_of_nonneg_left he (mul_nonneg ‹0 < c›.le hf'.le)).trans_eq ?_; unfold B; change c * ((w i)^ (3:ℕ))⁻¹ * _= _; field_simp; ring
    constructor; swap; · exact (((Run.token hX _).addR hX hf).Ypow hX p|>.Ymul hX hk)
    intro a; let n:ℝ:= (p+10:ℕ); have hn:0<n:= Nat.cast_pos.mpr (Nat.zero_lt_succ ..); refine ((Van.castE hX (neg_lt_zero.mpr (inv_pos.mpr hn))) a).cash ?_; filter_upwards [hw.eventually_gt_atTop 0] with i hi
    rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; have he : w i≤ y i:=Nat.le_ceil _; have hv:0≤ St i:=by unfold St thorn αm; exact div_nonneg (zpow_nonneg hi.le _) hn.le
    have ht:(w i)^4 ≤ (spotN (X i): ℝ):=by unfold spotN; rw [Nat.cast_pow]; exact pow_le_pow_left₀ hi.le he 4
    change -St i * _ ≤ -n⁻¹*w i; apply (mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr hv)).trans_eq; unfold St thorn αm; rw [_root_.zpow_neg]; change -(((w i)^ (3:ℕ))⁻¹/n)*_= _; field_simp
lemma rawG : Run φ X (fun i=> (skirt (spotN (X i)):ℝ)) 0 :=by
     have ht(i):spotN (X i)=(Nat.ceil (hatW (X i)))^4:=rfl
     have hh:Run φ X (fun i=>(radiusB (X i):ℝ)) 0:= Run.Yceil hX (Run.stanza hX) (Eventually.of_forall fun i=>sq_nonneg _)
     have hp:Run φ X (fun i=>(spotN (X i):ℝ)) 0:=by unfold spotN; push_cast; exact hh.Ypow hX _
     unfold skirt; push_cast; exact ((hp.addR hX hp).addR hX (Run.token hX _)).Ypow hX _
lemma facing : let Φ:= Y; Run φ Φ (fun i=> ((keepF (A i).F (x' i)).card:ℝ)) 0∧Run φ Φ (fun i=> ((keepB (A i).F (x' i) G).card:ℝ)) 0∧ Run φ Φ (fun i=> (Fintype.card (Lake (A i).F (x' i) G):ℝ)) 0:=by
     let F(i):= (A i).F; intro Xv; have hx:Tendsto Xv φ atTop:= (Work.E09.betaF_growth G K.L).comp hX
     let V(i):= board (F i) (x' i); let x(i):ℕ:= skirt (spotN (Xv i)); have hP : Run φ Xv (fun i=>(x i:ℝ)) 0:= rawG hx; let f(i):= keepF (F i) (x' i);
     have ht : Run φ Xv (fun i=> ((V i).card:ℝ)) 0:=by
          refine (hP.mulY hx 4).cash (Eventually.of_forall (fun i=>?_)); rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (V i).card)]; apply le_trans _ (le_abs_self _); exact_mod_cast (le_trans (show (V i).card≤ (x' i).card*4 from boardC (F i) _) (Nat.mul_le_mul_right _ (caseX (z i) _)))
     have hh' :Run φ Xv (fun i=>(Fintype.card (Lake (A i).F (x' i) G):ℝ)) 0:= by unfold Lake; simp_rw [Fintype.card_prod,Fintype.card_coe,Nat.cast_mul]; exact ht.mulY hx _
     constructor; · refine ht.cash (Eventually.of_forall (fun i=>?_)); rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (f i).card)]; exact (Nat.cast_le.mpr (Finset.card_image_le (s:=V i) (f:=fun i=> (i.val.1,Exterior.coord i.val.2)))).trans (le_abs_self _)
     refine ⟨hh'.cash (Eventually.of_forall fun i=> ?_),hh'⟩; rw [abs_of_nonneg (Nat.cast_nonneg .. : 0 ≤ ((keepB (A i).F _ G).card:ℝ))]; apply le_trans _ (le_abs_self _); exact_mod_cast (le_trans (show (keepB (F i) (x' i) G).card≤_ from Finset.card_image_le) (Finset.card_univ.le))
end Issue
end YM.MSbar.Mosaic
