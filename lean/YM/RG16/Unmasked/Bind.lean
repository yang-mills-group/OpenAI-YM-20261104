import YM.RG16.Unmasked.Report
import YM.RG16.Unmasked.Retained

/-!
# Binding true report to the budgeted replica array

Origin fields for q-ass comparison require using *true* germ-projected
return (`y` below) rather than an arbitrary z giving good RootBound.
We reuse bequeath on the actual volume, retaining live representation at
full tiling. It gives root norm of the cylinder and price on the
**representation**. Then get intrusion of the page's wraps under control
at u with readPage_eq; THIS will make eventual small coupling errors usable
on only a single copy, while keeping replication out of the high order
precision budgets. Keep every density equality (needs them pointwise on the
torus field space, with no mask stripped).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Literal
open Function Filter Set MeasureTheory Lattice Wilson RG Source Marker Extra.Histories
open Extraction Next.Rank Push Push.GridApprox
open Extra.Histories.Relay MergeProof MergeProof.Accent Bid Cells Motion
open Extra.Trajectories Extra.Multi Overlay Exponential Edition
open Planned.GuardedAtom Push.Local MergeProof.Float
open Trace.Physical.GermGraph
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge} (C:Family G) (N p d b u J:ℕ)
local notation "R" => C.path.rep N p
local notation "F" => C.labels.level d
local notation "H" => C.path
local notation "n" => Site (C.side J p)
local notation "B" => Stock.census (Site (C.side J p))
local notation "o" => Mix.camp C p J
local notation "μ" => hands C p J

abbrev Fleet (f:Cut C N p) (hi:J ≤ N) (w:Site (C.side J p)→ℝ) (q:store C d p b) (hn:b≤N) :=
  Served (R b) (fun i=> radiant (alto C.path b d) (μ i) (o b i)
    (q.exponentialEntry 0 (C.localSection d) (R b)))
    (fun i=> sunny (R b) q.forced (μ i) (o b i) (alto C.path b d))
    (gust C.path N p N
      (birth B (R N) (fun i=> (center C.S p hi 0).copy i f)) b hn)
    (o b) w (C.path.levels.budget b).supportExponent 1

/-- Read the same Q's exact denotation from the funded replica assembly. Thus
subsequent re-expressions for perturbative bookkeeping can stay on the full
actual path without imposing any new address-level per-term charges in this
assembly. (Such a rerender could be done separately per representation when
keeping evaluated SAME density; not permissible to substitute it here and use
the original Fleet on it.) -/
lemma Fleet.keeps (h:C.Makes) (f:Cut C N p)(hf:Continuous f)(hj:J≤b)(hn:b ≤ N)
   (w:Site (C.side J p)→ℝ) (q: store C d p b){r:ℝ}(hq: reads d N p b q r)
   (ht:Fleet C N p d b J f (hj.trans hn) w q hn):
   credit C N p d f b hn=value (C:=C) d N p b q := by
  choose k hK hD hE using fun i : n =>
    MergeProof.sparkling H C.params (C.localSection d) q (μ i) (o b i) (alto H b d)
      h.wilson 0 hn (h.sections d) hq.1 hq.2
  let T:= center C.S p (hj.trans hn) 0
  let Y:= birth B (R N) (fun i=> T.copy i f)
  have hA : ∀ i : T.Cell, Continuous (T.copy i f) := by
    intro i; unfold Tiling.copy; split; exact (hf.comp (continuous_pull ..)).star; exact hf.comp (continuous_pull ..)
  have hx:Integrable Y (prior G _):= (hatCont C N p _ hA (show Continuous ((R N).eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) (B)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let t := (B).fire 0
  unfold Fleet at ht
  simp_rw [hK] at ht
  have hr1 : (fun U=>(Y U).part t)=fun U=>(bare (C.beta N p) U:ℂ)*f U := by
    funext U; unfold Y Accent.birth Mach
    rw [Poly.part_smul,pass_fire]
    change ((R N).eval U:ℂ)*(∏ i∈ ({0}:Finset (n)), T.copy i f U)=_
    rw [Finset.prod_singleton]
    change ((R N).eval U:ℂ)*(T.copy 0 f U)=_
    rw [T.copy_zero,(h.wilson.starts ..).2]
  have hr := gust_choose H N p _ hx hn t
  have hs : (fun U => (gust H N p N Y b hn U).part t)= radiant (alto C.path b d) (μ 0) (o b 0) (q.density 0 (C.localSection d) (R b)):= by
    funext U; exact ((MergeProof.Accent.Served.relay ht hD
      (h.wilson.represents N p b hn).good.labels U).1 0).trans (congr_fun (hE 0) U)
  rw [hs, hr1] at hr
  rw [credit,←hr]; unfold radiant
  rw [handmove C b p J hj]
  change (C.S.a b : ℂ)^d • alto C.path b d • ((center C.S p hj 0).copy 0 (q.density 0 (C.localSection d) (R b))) = value (C:=C) d N p b q
  rw [show (center C.S p hj 0).copy 0 (q.density 0 (C.localSection d) (R b)) = q.density 0 (C.localSection d) (R b) from funext fun U=> Tiling.copy_zero .., smul_smul, alto,
    mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')), one_smul]

local notation "terminal" => (C.factory d N p).terminal
section
variable {ψ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}
    {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
    {cost:ℕ → ℝ}
    (X : ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g:ℕ→ℝ}
    (h:C.Makes) (hu:Opened C d u p) (hn:u ≤ b) (hN:b ≤ N)
    (hh: Club C.path C.params (C.localSection d) (ζ d) ψ u b N p cost D X g hN)
    (f:Cut C N p) (hf:Continuous f) (z:C.label d)
    (hR: (X b).density 0 (C.localSection d) (C.path.rep N p b) = credit C N p d f b hN +
       ((C.factory d N p).entries b (-(C.factory d N p).terminal.symm z)).density 0 (C.localSection d) (C.path.rep N p b))
include hh hf hR hu h
-- price of translating wrap from z to the true page of f. Needs used
-- club density vote, not just the exposed root test.
lemma match_step (i:ℕ) (hi:u ≤ i)(hp:i≤b): credit C N p d f i (hp.trans hN)=
      value (C:=C) d N p i (X i)+calValues d N p i ((terminal).symm z) := by
    have hc:= hu.post
    induction hp using Nat.decreasingInduction with
    | self=>
      change value (C:=C) d N p b (X b) = _ + calValues d N p b (-(terminal).symm z) at hR
      have hb:= le_trans hu.post hi
      rw [hR,add_assoc]
      have hz : calValues d N p b (-(terminal).symm z)+calValues d N p b ((terminal).symm z)=0:= by
         rw [←cal_add d N p b h hb hN,neg_add_cancel]; exact zero_cal d N p _ h hb hN
      simp only [hz,add_zero]
    | of_succ i hp ih=>
      have hi':= hi.trans i.le_succ
      have hp':= hp.trans_le hN
      have hF:= hc.trans hi
      have he:= hh.ticks (i+1) hi' hp
      rw [credit_step C N p d f hf hp', ih hi']
      have hval : value d N p i (X i)=transition (C:=C) d N p i (value d N p (i+1) (X (i+1))):= (hh.votes _ hi hp).1
      have hq := message d N p _ h (hc.trans hi') hp' (show reads d N p (i+1) (X (i+1)) _ from he)
      have ht : Integrable (calValues (C:=C) d N p (i+1) ((terminal).symm z)) (prior G _):= message d N p _ h (hc.trans hi') hp' (entryOk d N p _ h (hc.trans hi') hp' ((terminal).symm z))
      rw [transition_add _ _ _ hq ht,hval,factory_eq d N p i h hF hp' ((terminal).symm z)]

include hn
lemma align {E:ℝ}(hP:g u+ (F).coeffSize (X u).x ≤ E/gainChart H b u) :
    (∀ i,u ≤ i →∀ hm:i≤b, Booked C N p d f i (hm.trans hN)) ∧
    mCost C d N p u (topReport C N p d h u hu (hn.trans hN) f-(terminal).symm z) ≤ E/gainChart H b u := by
  let c:= (terminal).symm z
  let v i:= (C.factory d N p).entries i c; let s i:=beside (X i) (v i)
  let p'(i) (hi:u ≤ i)(hp:i≤b): reads d N p i (v i) ((stock C i)*(F).coeffSize (v i).x):=
      entryOk d N p i h (hu.post.trans hi) (hp.trans hN) c
  let h'(i)(hi:u ≤ i)(hp:i≤b): reads d N p i (X i) (g i):= hh.ticks i hi hp
  have Hs(i)(ht:u ≤ i)(hm:i≤ b) := presentation (h' i ht hm).1 (h' i ht hm).2 (p' i ht hm).1 (p' i ht hm).2
  have Hprice(i)(ht:u ≤ i)(hm:i ≤ b): credit C N p d f i (hm.trans hN)=value d N p i (s i) := by
    rw [match_step C N p d b u X h hu hN hh f hf z hR i ht hm]
    exact (plus (h.wilson.represents _ _ _ (hm.trans hN)|>.good) (h' i ht hm).2 (p' i ht hm).2 (C.localSection d)).symm
  refine ⟨fun i ht hm=> ⟨s i,_,Hs i ht hm,Hprice i ht hm⟩,?_⟩
  have hx := readPage_eq C N p d f h (hn.trans hN) hu.post (s u) (Hs u le_rfl hn) (Hprice u le_rfl hn)
  change (F).coeffSize (fitting d N p u h hu (hn.trans hN) _) ≤ _
  unfold topReport; rw [map_sub, LinearEquiv.apply_symm_apply, hx, show fitting d N p u h hu (hn.trans hN) ((terminal).symm z) = page d p u (v u) from rfl,
     show page d p u (s u) = _ from addPage d N p u (X u) (v u) h hu.post (hn.trans hN) (h' u le_rfl hn) (p' u le_rfl hn), add_sub_cancel_right]
  let k:= X u; have hi := hu.post
  have hs:= measured_diff d N p _ h hi (hn.trans hN) (h' u le_rfl hn)
  have hl:= Size.add (F) k.x (page d p u k-k.x); rw [add_sub_cancel] at hl
  have hx:= smaller d p hu; have he:0≤g u:= rem_nonneg (h' u le_rfl hn).2
  have he := mul_le_of_le_one_left he (hx.trans (by norm_num))
  exact hl.trans ((add_le_add_right (hs.trans he) _).trans (le_trans (add_comm _ _).le hP))
end
end YM.RG16.Literal
