import YM.FVAAlt2.Aperture.Visit
import YM.Comparison.RG02.Adjacent.Warp
/-! # Crossing from θ program at true χ(t) to the common-chart reader; analytic comparison fixed, actual prefactor payments. Later take Fk sphere test. Note sign in price. Uses actual STEP kernel/W color not Ledger. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure Actual
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V] {R:Census V}(W:Bulk.Colors R G f)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ" => C.enter
local notation "H" => F.Slice G
local notation "Q" => K.covariance F w
open Classical
variable (t:ℝ) (x:fieldDir G c 1)
local notation "ζ"=> Bulk.translated K F x
open Laplace PertExtension.Series.Tested Symmetry Symmetry.Ribbon Trade LocalScript Moving Moving.Shift Moving.Path
variable (A:Set (F.Slice G))
def unitx(t:ℝ): X:= (C.rating t)⁻¹ • x -- coarse field coordinate in Fk
local notation:max "v_" g:max=> unitx C x g
lemma use (h:0<C.rating t): sample t x= sample (ρ t) (v_ t):= by unfold sample unitx UnitCost.enter; rw [smul_smul,mul_assoc,_root_.mul_inv_cancel₀ h.ne',mul_one]
lemma timeUnit : ContDiffAt ℝ ω (unitx C x) 0:= ((C.smooth.inv (by simp [C.origin])).smul contDiffAt_const)
lemma timeBase: v_ 0=x:= by unfold unitx; simp [C.origin]
-- slope mismatch (including chartCost)
abbrev dim := Fintype.card (Precision.Key F G)
local notation "n" => (dim F (G:=G) :ℝ)
local notation "E"=> Bulk.infrared S p P F w (K.b F)
-- not using Poly.power until after χ rescaling
def earn (g:ℝ):ℝ:= (dim F (G:=G):ℝ)* Real.log (C.rating g)
def bureau (g:ℝ):ℝ:= earn (G:=G) F C g+ E x- E (v_ g)
def entry (g:ℝ):ℂ := ↑(Real.exp (bureau K F w C x g))
local notation "L'"=> bureau K F w C x
local notation "U"=> entry K F w C x
-- dim fix lexical macro reused
lemma fine_time : ContDiffAt ℝ ω (earn (G:=G) F C) 0:= contDiffAt_const.mul (C.smooth.log (by simp [C.origin]))
lemma earning_zero : earn (G:=G) F C 0=0:=by simp [earn,C.origin]
lemma energetic: ContDiff ℝ ω E := by
    rw [show E = -(Complex.reCLM ∘ (Symmetry.price K F w)) from funext fun i=> (neg_neg _).symm]; exact (Complex.reCLM.contDiff.comp ( Symmetry.price_ready K F w )).neg
lemma pathT : ContDiffAt ℝ ω (bureau K F w C x) 0:= ((fine_time F C).add contDiffAt_const).sub ( (energetic K F w).contDiffAt.comp _ (timeUnit C x))
lemma origin0: L' 0=0:=by simp [bureau, earning_zero,timeBase]
lemma entryT: ContDiffAt ℝ ω (entry K F w C x) 0:= (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (pathT K F w C x).exp)
lemma paid (h:0<C.rating t): Real.exp (earn F C (G:=G) t)= (C.rating t)^dim F (G:=G):= by unfold earn; rw [Real.exp_nat_mul,Real.exp_log h]
lemma currency (ht:0<t)(hp:0<C.rating t): wage K F w (ρ t) 0 (v_ t) = priceT K F w C t x * Real.exp (bureau K F w C x t) :=by
    have h:0<ρ t:= mul_pos ht hp
    unfold bureau priceT; rw [paid_as, chartCost_eq (Q) h, chartCost_eq (Q) ht,show (ρ t)^_ = _ from (show (ρ t)^ dim F (G:=G)= t^dim F (G:=G) * C.rating t ^ dim F (G:=G) from mul_pow ..)]
    unfold one_tag standard calorie; simp only [zero_sub]; rw [ Real.exp_sub,Real.exp_add,paid F C t hp,Real.exp_neg, Real.exp_neg ] -- adjust add_assoc already
    ring_nf; rw [mul_assoc _ (Real.exp (E x)),mul_inv_cancel₀ (Real.exp_pos _|>.ne'),mul_one]
variable [Fintype V] (r:ℕ)
lemma portal_price (ht:0<t)(hp:0<C.rating t) : tale K F w C W t x A = U t • portal K F w 0 W (v_ t) (fun _=> A) (ρ t):=by
    have hx: (priceT K F w C t x : ℂ) ≠0:= Complex.ofReal_ne_zero.mpr (price_p K F w C t x ht).ne'; have he: ( entry K F w C x t :ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_pos _|>.ne')
    unfold tale portal actual0; rw [smul_smul, use C t x hp, currency K F w C t x ht hp,Complex.ofReal_mul]; rw [show (↑(Real.exp (L' t)):ℂ)=U t from rfl, show U t*_= _ from (show U t*( (priceT K F w C t x:ℂ)* (U t))⁻¹=( (priceT K F w C t x:ℂ))⁻¹ by rw [mul_inv]; field_simp)] -- rewrite
local notation "Ω"=> bank K F w C W x r
local notation "τ"=> fun (u: X)=> Fk K F w W u r
-- Alias.Binder. Positive coefficient

def knownClock (u:ℝ):Order.Grade R r:= Trade.course C 0 r (fun v=>Fk K F w W v r) x u
lemma known_convention (s:R.Mode)(hp:0<C.rating t) : (value (t:ℂ) (knownClock K F w C W x r t)).part s= (value (ρ t:ℂ) (Fk K F w W (v_ t) r)).part s:=by
    unfold knownClock; rw [Trade.paying C 0 r s (τ) x t hp]; unfold markDebt Adjacent.ages Adjacent.cover Adjacent.Trade.read; simp only [Pi.zero_apply,sum_const_zero,zpow_zero, Complex.ofReal_one,one_mul]; rw [vpart]; rfl

def fare (u:ℝ): Order.Grade R r:= heat R r (entry K F w C x) u * knownClock K F w C W x r u
lemma forecast (s:R.Mode): (value (t:ℂ) (fare K F w C W x r t)).part s=U t *(value (t:ℂ) (knownClock K F w C W x r t)).part s:=by
    unfold fare Ribbon.heat; rw [smul_mul_assoc,one_mul]; change (valueL R r _ _).part _= _; rw [map_smul,Marker.Poly.part_smul];rfl
lemma agency : Seen (fare K F w C W x r):= (heat_seen R r (entry K F w C x) (entryT K F w C x)).product (( accounts K F w W r ).describes C 0 r x)
lemma worthy : ∀ᶠ t in 𝓝 (0:ℝ),Order.Symmetric (fare K F w C W x r t):= Eventually.of_forall fun t=> (heat_save R r U _).mul (chosen C 0 r _ _ ( Bulk.fk_sym K F w W (v_ t) r ))
-- shape for Trial
lemma price_b (s:R.Mode) : ContDiffAt ℝ ω (fun t:ℝ=> (value (t:ℂ) (fare K F w C W x r t)).part s) 0 := by
    simp_rw [vpart]; exact ContDiffAt.sum fun i _ => (Complex.ofRealCLM.contDiff.contDiffAt.pow i).mul (Moving.Shift.watch (agency K F w C W x r) s i)

end YM.Comparison.RG02.FVAAlt2.Aperture
