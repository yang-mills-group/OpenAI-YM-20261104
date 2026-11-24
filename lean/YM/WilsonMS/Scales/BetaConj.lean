import YM.WilsonMS.Scales.SpanPsi
/-!
# Unique transport of the dilation operation through f and Z

In particular the coupling rescaling seen by MS, at all physical fields, is
forced by the calibrated relation (without fixing a rank auxiliary Cn).
Keeps engineering weights. Formal units and leading coefficients: simultaneous
grade and H. Scaling on coupling proven even before
passage to differential equations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
section Aw
variable {Q c p x : Cn} (h : Aware Q)

lemma pinsX {F : ChartK G d} : Sub X F = F := by
  funext n v
  apply FrameConj.byRanks
  intro p
  rw [show _ = _ from FrameConj.readMove Aware.identity.root (F n v) p, pcomp]
  exact PowerSeries.X_subst _
include h

lemma Aware.undo : Q.subst (Counter Q) = PowerSeries.X :=
  Ice.counter_l h.root
    (by
      rw [h.paid]
      norm_num)

lemma Aware.unravel : PowerSeries.subst Q (Counter Q) = PowerSeries.X :=
  Ice.counter_r h.root
    (by
      rw [h.paid]
      norm_num)

lemma Aware.off (hx : p.subst Q = x.subst Q) : p = x := by
  obtain hv := congr_arg (fun i : Cn => i.subst (Counter Q)) hx
  change PowerSeries.subst _ _ = _ at hv
  rw [Ice.assoc h.root (born _), Ice.assoc h.root (born _), h.undo, PowerSeries.X_subst,
    PowerSeries.X_subst] at hv
  exact hv

lemma Aware.offR (hp : Rooted p) (hx : Rooted x) (he : Q.subst p = Q.subst x) : p = x :=
  Ice.separate h.root
    (by
      rw [h.paid]
      norm_num)
    hp hx he

lemma ring_inj {P T : Guard G d} (hc : coupon Q P = coupon Q T) : P = T := by
  apply PowerSeries.ext
  intro n
  ext1 x
  apply (dime G d).repr.injective
  ext1 i
  obtain he := congr_arg (fun p => Normalize.tax p x i) hc
  rw [coupon_paid h.root, coupon_paid h.root, pcomp, pcomp] at he
  obtain hh := congr_arg (coeff n) (h.off he)
  simp only [Normalize.tax, PowerSeries.coeff_mk] at hh
  exact hh
omit h

lemma CloseP.stiff {P : Guard G d} (hP : Mass P) (A : Cn) : Mass (coupon A P) := by
  refine PowerSeries.ext fun i => ?_
  rw [printed]
  unfold coupon
  simp only [PowerSeries.coeff_mk, rules]
  rw [tile_total]
  refine Finset.sum_congr rfl fun j _ => ?_
  let x := cut A j i
  let V := coeff j P
  suffices hL : shadows (x • V) = x • shadows V
    by
    rw [show _ = _ from hL]
    exact congr_arg (x • ·) (hP.exactly j)
  ext1 p
  rw [levy, LinearMap.smul_apply (x := p), levy]
  simp_rw [LinearMap.smul_apply, map_smul, Finset.smul_sum]

lemma Mass.anti {P : Guard G d} (hP : Mass P) (hx : CloseP P) : Mass (vault P) := by
  have he := print_prod hx hx.invert
  rw [antidote hx |>.1, hP, print1] at he
  exact hx.1.seed.mul_right_inj.mp (he.symm.trans (antidote hx).1.symm)
end Aw

section path
variable {X Z : Scheme G} {t : ℝ} {B R U : Links G} {F H K W : Cn}

private def transported (s : ℝ) (p : Links G) (Q : Cn) (U : Links G) (W : Cn) : Links G := fun d =>
  vault (buryD s (p d)) * coupon Q (U d) * coupon W (p d)

lemma alongK {f g : Cn} (hv : Aware f) (hh : Aware g) (hp : ∀ d, CloseP (R d))
    (he : ∀ d, Equad (X d) (Act (Sub f (Z d)) (R d))) (h : Linked Z t U F)
    (hr : f.subst g = F.subst f) : Linked X t (transported t R f U g) g := by
  refine
    ⟨fun d =>
      ((duties t (hp d)).invert.times ((h.ground d).substitute hv.clean)).times
        ((hp d).substitute hh.clean),
      hh, fun d => ?_⟩
  let P d := transported t R f U g d
  obtain hz := (sweep_t (he d) t).act (P d)
  obtain hZ := Equad.sub (he d).symm g
  apply hz.trans (Equad.trans _ hZ)
  rw [adjoint, ← name_sub t hv.root, action_times,
    show buryD t (R d) * P d = coupon f (U d) * coupon g (R d) from ?_, ← action_times, ←
    action_sub hv.root, action_sub hh.root, sub_subK _ hv.root hh.root, hr, ←
    sub_subK _ h.normal.root hv.root]
  · exact Equad.act (Equad.sub (h.origin d) f) _
  unfold P transported
  rw [← mul_assoc, ← mul_assoc, (antidote (duties t (hp d))).1, one_mul]

lemma reflection (h : ∀ d, Equad (X d) (Act (Z d) (R d))) (hp : ∀ d, CloseP (R d)) :
    ∀ d, Equad (Z d) (Act (X d) (vault (R d))) := by
  intro d
  obtain he := (h d).symm.act (vault (R d))
  rwa [action_times, (antidote (hp d)).1, action_unit] at he
end path
variable {M : Booked (Ensure.deck G)} {F : MS_Data G M} {V : Store G} (P : Rose.Pick V) {t r : ℝ}
  {W : Initialize G}

abbrev muFlow (P : Rose.Pick V) (F : MS_Data G M) (t : ℝ) : Cn :=
  (ψW P F).subst (PowerSeries.subst (χMS 0 P F) (transit P F t))

def Z_back (P : Rose.Pick V) (F : MS_Data G M) (d : ℕ) :=
  vault (coupon (χMS 0 P F) (Zx P F d))

def frameMS (P : Rose.Pick V) (F : MS_Data G M) (t : ℝ) : Links G :=
  transported t (Z_back P F) (χMS 0 P F) (β_frame P F t) (muFlow P F t)
variable (hG : G.Simple) {X : Prescription (Ensure.deck G)} (hp : Installed W F X) (hh : Commuting X)
include hG hp hh

lemma βμ_rescale (t : ℝ) : Aware (muFlow P F t) :=
  (ψ_aware P hG hp hh).extend ((flowAware P hG hp hh t).extend (awareχ P hG hp hh 0))

lemma scaleMS_f (t : ℝ) :
    PowerSeries.subst (ψW P F) (muFlow P F t) = (ψW P F).subst (transit P F t) := by
  obtain he := awareχ P hG hp hh 0
  have ht := flowAware P hG hp hh t
  unfold muFlow
  rw [Ice.assoc (ht.extend he).root he.counter.root, Ice.assoc he.root he.counter.root, he.undo,
    Ice.eraser]

lemma Earnings (t : ℝ) : Linked (GMS F 0) t (frameMS P F t) (muFlow P F t) := by
  obtain hv := awareχ P hG hp hh 0
  obtain hl := ψ_aware P hG hp hh
  let U := finale P F
  let c := χMS 0 P F
  let r := ψW P F
  have hL (d : ℕ) : Sub c (U d) = Act (GMS F 0 d) (coupon c (Zx P F d)) := by
    unfold U
    rw [Ck P hG hp hh, action_sub hv.root, sub_subK _ hl.root hv.root, hv.unravel, pinsX]
  have ht (d : ℕ) : CloseP (coupon c (Zx P F d)) := (neutral P hG hp hh _).substitute hv.clean
  apply
    alongK hv (βμ_rescale P hG hp hh t) (fun d => (ht d).invert)
      (reflection (X := fun d => Sub c (U d)) (fun d => (hL d).symm ▸ Equad.rfl _) ht)
      (kinetic P hG hp hh t)
  unfold muFlow
  rw [← Ice.assoc hl.root (((flowAware P hG hp hh _).extend hv).root), hv.undo,
    PowerSeries.subst_X ((Worried (((flowAware P hG hp hh _).extend hv).root)))]

lemma grand (t : ℝ) (d : ℕ) : Mass (frameMS P F t d) := by
  obtain h := Earnings P hG hp hh t
  apply
    power_mass hG (h.ground d) ((global_P F 0).spun t)
      (((global_P F 0).subs h.normal.root).pass (h.origin d).symm)
  intro s n x hx
  rw [lands, starClock F 0 (s + t) d n hx, rooted_flow _ _ _ _ _ hx]

private lemma pin_back (t : ℝ) {U : Cn} {P' : Links G} (h : Linked (GMS F 0) t P' U) :
    let r : Cn := PowerSeries.subst (U.subst (ψW P F)) (χMS 0 P F)
    transported t (FrontMS P F) (ψW P F) P' r = changeM P F t ∧ r = transit P F t := by
  intro r
  apply single P hG hp hh
  obtain H := ψ_aware P hG hp hh
  obtain hx := awareχ P hG hp hh 0
  have hL := h.normal.extend H
  apply alongK H (hx.extend hL) (front_close P hG hp hh) (X := (ΨScheme P F)) _ h
  · rw [← Ice.assoc hx.root hL.root, hx.unravel, PowerSeries.subst_X (FrameConj.Worried hL.root)]
  intro d
  rw [show ΨScheme P F d = Act (Sub (ψW P F) (GMS F 0 d)) (FrontMS P F d) from
      Eq.trans rfl (action_sub H.root _ _)]
include P

lemma inherent (t : ℝ) {U W : Cn} {X' Y : Links G} (h : Linked (GMS F 0) t X' U)
    (hx : Linked (GMS F 0) t Y W) : X' = Y ∧ U = W := by
  obtain ⟨hp', hC⟩ := pin_back P hG hp hh t h
  obtain ⟨hz, hr⟩ := pin_back P hG hp hh t hx
  have hF := ψ_aware P hG hp hh
  have hi : U = W :=
    hF.off
      ((awareχ P hG hp hh 0).offR ((h.normal.extend hF).root) ((hx.normal.extend hF).root)
        (hC.trans hr.symm))
  subst U
  refine ⟨funext fun i => ?_, rfl⟩
  obtain ht := congr_fun (hp'.trans hz.symm) i
  let R := ψW P F
  let T := W.subst R
  let a := PowerSeries.subst T (χMS 0 P F)
  have hS :=
    (front_close P hG hp hh i) |>.substitute
      ((awareχ P hG hp hh 0).extend (hx.normal.extend hF)).clean
  have hk := (duties t (front_close P hG hp hh i)).invert
  exact ring_inj hF (hk.1.seed.mul_right_inj.mp (hS.1.seed.mul_left_inj.mp ht))

lemma μTicks (t s : ℝ) : PowerSeries.subst (muFlow P F t) (muFlow P F s) = muFlow P F (s + t) :=
  (inherent P hG hp hh (s + t) (Linked.twirl (Earnings P hG hp hh t) (Earnings P hG hp hh s))
      (Earnings P hG hp hh _)).2

lemma fieldsTicks (t s : ℝ) (d : ℕ) :
    buryD s (frameMS P F t d) * coupon (muFlow P F t) (frameMS P F s d) = frameMS P F (s + t) d :=
  congr_fun
    (inherent P hG hp hh (s + t) (Linked.twirl (Earnings P hG hp hh t) (Earnings P hG hp hh s))
        (Earnings P hG hp hh _)).1
    d

lemma Υtest {p : Cn} {A : Links G} (hv : Aware p) (hU : ∀ i, CloseP (A i))
    (hx : ∀ d, Equad (Act (Sub p (GMS F 0 d)) (A d)) (finale P F d)) : A = Zx P F ∧ p = ψW P F := by
  have hr := ψ_aware P hG hp hh
  have hβ := awareχ P hG hp hh 0
  have he (d : ℕ) :
    Sub (PowerSeries.subst p (χMS 0 P F)) (ΨScheme P F d) =
      Act (Sub p (GMS F 0 d)) (coupon p (KnotMS F V 0 d)) := by
    rw [← sub_subK _ hβ.root hv.root, ← action_sub hv.root]
    refine congr_arg (Sub p) ?_
    change Sub _ (Sub _ (Act _ _)) = _
    rw [sub_subK _ hr.root hβ.root, hβ.unravel, pinsX]
    rfl
  let B : Cn := PowerSeries.subst p (χMS 0 P F)
  let U i := uprightN P F i
  have hM (i : ℕ) : Equad (Act (Sub p (GMS F 0 i)) (A i * vault (U i))) (ΨScheme P F i) := by
    obtain H := (hx i).act (vault (U i))
    unfold finale revising at H
    rwa [action_times, action_times, (antidote (freeN P hG hp hh i)).1, action_unit] at H
  have ht (i : ℕ) : A i * vault (U i) = coupon p (KnotMS F V 0 i) :=
    BasisTest.forcing V (hM i) (W := coupon p _) (T := Sub B (ΨScheme P F i))
      (by
        unfold B
        rw [he i])
      (ψCert P hG hp hh i) (BasisTest.styled _ (ψCert P hG hp hh i) (hβ.extend hv))
      ((hU i).times (freeN P hG hp hh i).invert) ((knot_base ..).substitute hv.clean)
  have hpB : Equad (ΨScheme P F 6) (Sub B (ΨScheme P F 6)) := by
    unfold B
    rw [he, ← ht 6]
    exact (hM 6).symm
  obtain hB := obs_equ P hpB
  rw [ob_sub P (hβ.extend hv).root (fitted P F 6 3), watches P hG hp hh,
    PowerSeries.subst_X (Worried (hβ.extend hv |>.root))] at hB
  have he' : p = ψW P F := hβ.offR hv.root hr.root (Eq.trans hB.symm hβ.undo.symm)
  refine ⟨?_, he'⟩
  ext1 d
  rw [show Zx P F d = _ from congr_fun (recallZ P hG hp hh) d]
  apply (freeN P hG hp hh d |>.invert).1.seed.mul_left_inj.mp
  rw [mul_assoc _ (U d), (antidote (freeN P hG hp hh d)).1, mul_one, ht, he']
end YM.WilsonMS.GFlow
