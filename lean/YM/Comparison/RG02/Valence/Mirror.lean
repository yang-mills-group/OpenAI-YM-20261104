import YM.Comparison.RG02.Valence.Volume
import YM.Comparison.RG02.Bulk.Spur
/-!
# Reflection test (parity) at fixed fine units.

 This is not group-link inversion! Reflect g at every argument BEFORE rescaling external fields.
 Constant-turn geometry remains unchanged. For marks, impose their own parity inputs; moving
 coupling resets must then re-check parity. No similar symmetry asserted on true path history
 functions varying in temperature. Sign for weight `ξ` general (if unsupported by input vertex
 true sign likely both sides zero). -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence.Mirror
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick Order Join Bulk Assembly
open YM.Extra.Trajectories (connected)
open YM.Next.Rank YM.Next.SectorChange Gaussian
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

private lemma mirror_cloud {J:Type} [DecidableEq J] [Fintype J] (Q : Gaussian.Table J) (h : Q.PosDef) (f : (J→ℝ)→ℂ) : (∫ v, f (-v) ∂cloud Q)=∫ v,f v ∂cloud Q:= by
   let s x:= Real.exp (-(force Q x/2)); let g x:=s x • f x; let u:(J→ℝ)≃ᵐ(J→ℝ) := (Homeomorph.neg _).toMeasurableEquiv
   have hs(x:J→ℝ): s (-x)=s x:=by simp [s,force,Matrix.mulVec_neg]
   have he (x:J→ℝ) (y:ℂ): Real.exp (force Q x/2) • (s x • y)=y:= by unfold s; rw [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
   have hm: MeasurePreserving u volume volume:= Measure.measurePreserving_neg ..; have hg (x): Real.exp (force Q x/2) • g (u x)=f (-x):= by unfold g; rw [show u x= -x from rfl,hs,he]
   have hf:= hm.integral_comp u.measurableEmbedding g; have h1:= (under_cloud h g).2; have h2:= (under_cloud h (fun x=>g (u x))).2
   dsimp only at h2 h1; simp_rw [hg] at h2; unfold g at h1; simp_rw [he] at h1
   exact (smul_right_inj (coat_pos h).ne').mp ((h2.symm.trans hf).trans h1)

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
local notation "B"=> Board R r
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Tree.Forest S.ratio) (w : S.Choices) (W : Bulk.Colors R G f)
  (ξ : V→ℂ) (x : fieldDir G c 1) (r:ℕ) (i:R.Mode)
local notation "X" => fieldDir G c 1
local notation "E" => Bulk.Joint S F (G:=G)
local notation "L" => geometric K F w W
local notation "Y" => markFn S F W
local notation "Δ" => dilation (Board R r) (Sum.elim ξ (fun _=>(-1)))
local notation "q" => K.covariance F w

def shape (k:ℕ) := (-1:ℂ)^k* ∏ a∈i.val,ξ a

def Calm (W : Colors R G f) := ∀ t,Hflip W.vac t
where Hflip f t := f (-t)=f t
structure Sound : Prop where
 vac : Calm W
 mark s t : W.mark s (-t)= shape ξ s.val (W.power s) • W.mark s t

private def μ: E→L[ℝ] E := (-(ContinuousLinearMap.fst ℝ ℝ (Bulk.SliceDir S F G))).prod (ContinuousLinearMap.snd ℝ ℝ (Bulk.SliceDir S F G))
omit [Fintype V] in
private lemma flip_price (h : Calm W) : L ∘ (μ (F:=F))=L:= by
   funext z; rw [Function.comp_apply]
   have hz: (μ (G:=G) F z).1=-z.1:= rfl; unfold geometric stone fee pillar officer supplement posed
   rw [show (μ (G:=G) F z).2=z.2 from rfl,hz,show W.vac (-z.1)=_ from h _,neg_sq]
omit [Fintype V] in
private lemma flip_index (h : Sound W ξ) (s : Hot R) : Y s ∘ (μ (F:=F))= (shape ξ s.val (W.power s)) • Y s := by funext z; exact congrFun (h.mark s z.1) (Work.F03.live F z.2)

private lemma direction (z : Precision.Key F G→ℝ) : translate (stage K F (-x)) (hinge F) (-z)=(μ (G:=G) F) ((-1:ℝ) • translate (stage K F x) (hinge F) z) := by
   change translated K F (-x) (-z)= μ (G:=G) F _; rw [footing,show Assembly.translate (stage K F x) (hinge F) z= translated K F x z from rfl,footing];
   rw [map_neg,neg_one_smul]; ext1
   · exact (neg_neg _).symm
   rw [show tape (G:=G) (-z) = -tape z from gaugeCount.map_neg z,← neg_add]; rfl
private lemma port (t:R.Mode)(i:Index r): (∏ a∈(pair t i).val, Sum.elim ξ (fun _=> -1) a)=shape ξ t i.val.card:= by simp [shape,pair,prod_disjSum,mul_comm]
private lemma calm (k:ℕ): (-1:ℂ)^k * (-1:ℂ)^k=1:= by rw [← mul_pow]; simp
variable {K F w x W ξ} (hK : Well W) (hW : Sound W ξ)
local notation "ℓ"=> affine W.power Y (L)
omit [Fintype V] in
include hK in
private lemma geometric_smooth : ContDiffAt ℝ ω (L) 0:= (stone_smooth K F w).add (fee_starts K F W hK|>.smooth)

include hK hW
private lemma ex (z : Precision.Key F G→ℝ) (x:X) : Δ (series R r (ℓ (translate (stage (S:=S) K F x) (hinge F) z)))=
    series R r (ℓ (translate (stage K F (-x)) (hinge F) (-z))) := by
   rw [direction K F x z]
   let u:E:= translate (stage K F x) (hinge F) z
   let y:= (-1:ℝ) • u; let v:= μ (G:=G) F y
   apply Join.both_parts; intro t i
   rw [dilation_part,polarization,port,polarization]
   let k:=i.val.card
   have he:vacuumLetter L v k=(-1:ℝ)^k* vacuumLetter L u k := by
      have ht : Assembly.jet L (k+2) v= _:= (jet_continuous_right (μ (G:=G) (F:=F)) ((geometric_smooth hK).of_le le_top) y).symm
      rw [flip_price K F w W hW.vac (p:=p)] at ht
      unfold vacuumLetter; split; rw [mul_zero]; rw [ht,(show Assembly.jet L (k+2) y=_ from Clipper.weight u (-1) (k+2) L),pow_add,show (-1:ℝ)^2=1 by norm_num,mul_one,smul_eq_mul,mul_neg]
   have hz (s:Hot R) : markLetter W.power Y s v k=shape ξ s.val k*markLetter W.power Y s u k:= by
      let g: ℂ→L[ℝ]ℂ:= ContinuousLinearMap.mul ℝ ℂ (shape ξ s.val (W.power s))
      have hi: ContDiffAt ℝ (↑(W.power s+k):ℕ∞ω) (Y s) 0 := (joint_receipt S F (hK.suppose_mark s)).smooth.of_le le_top
      have hh: Assembly.jet (Y s) (W.power s+k) v=shape ξ s.val (W.power s) * Assembly.jet (Y s) (W.power s+k) y := by
          rw [← jet_continuous_right (μ (F:=F)) hi y, flip_index ..,show shape ξ s.val (W.power s) • Y s=g ∘ Y s from rfl, ← jet_apply_left g _ _ hi]; rfl
          exact hW
      unfold markLetter; rw [hh,show Assembly.jet (Y s) (W.power s+k) y= _ from Clipper.weight u (-1) _ (Y s), Complex.real_smul]; unfold shape; push_cast; rw [pow_add,show ∀ b c d e : ℂ, b*c*(b*d*e)= b*b*(d*c)*e from fun _ _ _ _=> by ring,calm, one_mul]
   simp only [Assembly.affine, map_add,Poly.part_plus,realCoeff,beads]
   by_cases ha:t.val.Nonempty
   · let s:Hot R:=⟨t,ha⟩; rw [if_neg ((hot_iff_ne _).1 ha),if_neg ((hot_iff_ne _).1 ha),zero_add,zero_add]; unfold curve; rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk,show ∀ g:Hot R→ℂ,(lit R g).part t=g s from fun g=> part_lit g s,show ∀ g:Hot R→ℂ,(lit R g).part t=g s from fun g=> part_lit g s];
     change shape ξ s.val k*((k.factorial:ℂ)*markLetter W.power Y s u k)=(k.factorial:ℂ)*markLetter W.power Y s v k; rw [hz]; ring
   replace ha : t=R.quiet := of_not_not (mt (hot_iff_ne t).2 ha); subst t; rw [mark_curve_quiet,mark_curve_quiet, add_zero,add_zero, if_pos rfl, if_pos rfl]; change _=(k.factorial:ℂ)* ↑(vacuumLetter L v k); rw [he,shape]; change _* ((k.factorial:ℂ)* ↑(vacuumLetter L u k))=_; simp only [Census.quiet,prod_empty]; push_cast; dsimp only [k]; ring

lemma exponent (z : Precision.Key F G→ℝ) (x:X) : Δ (series R r (expansions W.power Y L (translate (stage (S:=S) K F x) (hinge F) z)))=
    series R r (expansions W.power Y L (translate (stage K F (-x)) (hinge F) (-z))) := by
   simp_rw [exponent_identity]; rw [pass_map _ _ (driver_quiet ..) ((quiet_dilation _ _).trans (driver_quiet ..)),ex]
   exacts [hK,hW]

local notation "Ω" x => Fk K F w W x r
lemma fk (x:X): Δ (Ω x)=Ω(-x):= by
   ext i; rw [dilation_part,Bulk.Fk,Bulk.Fk]
   rw [(Assembly.contracted (stage K F x) (hinge F) _ _ (geometric K F w W) _ _ (K.positive F w) r i).2, (Assembly.contracted (stage K F (-x)) (hinge F) _ _ (geometric K F w W) _ _ (K.positive F w) r i).2,← integral_const_mul]
   nth_rw 2 [← mirror_cloud q (K.positive F w)]
   apply integral_congr_ae; filter_upwards with z
   exact congrArg (Poly.part · i) (exponent (w:=w) r hK hW z x)

end YM.Comparison.RG02.Valence.Mirror
