import YM.RG17.Beads
import YM.RG17.Placement
import YM.RG17.Stairs
/-!
# Moor an aux L ANY real tail at reachable length all time from same Coverage.
 Now Stands is useful for comparison-support geometry. No assertion
 that this frame reads ANY finite perturbative law at that length.
 `/r` prices literal here; polynomial in H, NOT Lambda.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace RG12
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
   {u:Filter (ℕ×ℕ)} (U:Lenses.Mantle F u) (L:Layout F)(E:Services C f S) (fx:Flick C.path.levels)
set_option quotPrecheck false
local notation "H"=> C.path.levels.clock.hatBeta
local notation "a"=> C.S.a
local notation "M"=> L.charts
local notation "ρ"=> OPE.run
local notation "Λ"=> Allow.Lambda C
private lemma aside {z:ℕ→ℝ} (h:StrictAnti z)(ht:∀ i,0<z i)(Q:ℝ→Prop)
    (hQ:∀ᶠ i in atTop,Q (z i)) (hp:∀ᶠ i in home,i∉ Set.range z → Q i) : ∀ᶠ i in home,Q i:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp hQ
   filter_upwards [hp,(nhdsWithin_le_nhds (ge_mem_nhds (ht N)) : ∀ᶠ i in home,i ≤ z N)] with i he hm
   by_cases hh:i ∈ Set.range z; swap; exact he hh
   obtain ⟨m,rfl⟩:= hh; exact hN _ (h.le_iff_ge.mp hm)
variable {p q:ℝ→ℕ}
def Moored (C:Family G)(p:ℝ→ℕ) : Prop:=∀ᶠ r in home,C.S.a (p r) ≤ r ∧ r ≤ C.S.a (p r)*C.path.levels.clock.hatBeta (p r)^2
include E fx
lemma patchM (s:Extraction.Sequence)(hs:StrictAnti (U.radius ∘ ⇑s)) : ∃ p:ℝ→ℕ, Reach C p ∧ Moored C p ∧ ∀ i:ℕ,p (U.radius (s i))=s i:=by
   let z:= U.radius ∘ ⇑s
   let w:=locale C 0
   let p (r:ℝ):ℕ:= if h:r∈ Set.range z then s h.choose else w r
   have hp(i:ℕ): p (z i)=s i := by
       rw [show p (z i)=_ from dif_pos (Set.mem_range_self i)]; exact congr_arg _ (hs.injective (Classical.choose_spec (mem_range_self i : ∃ j, z j=z i)))
   have ht i :0 < z i:= U.positive _
   have hz: Sized C 0 w := ranks C E.simpleGate 0 fx
   have hv:= hz.reach C 0 w
   refine ⟨p,⟨tendsto_atTop.mpr ?_, Metric.tendsto_nhds.mpr ?_⟩,?_,hp⟩
   · intro n; apply aside hs ht
     · filter_upwards [s.cofinal.eventually_ge_atTop n] with i hi; change n ≤ p (z i); rw [hp i]; exact hi
     filter_upwards [hv.growing.eventually_ge_atTop n] with i hi ht; change n ≤ p i; rw [show p i=w i from dif_neg ht]; exact hi
   · intro ε he; apply aside hs ht
     · filter_upwards [s.cofinal.eventually (Metric.tendsto_nhds.mp (retainedPaid U) ε he)] with i hi; change dist (C.S.scale (p (z i))/ _) (1:ℝ)<ε; rw [hp]; exact hi
     filter_upwards [Metric.tendsto_nhds.mp hv.nearby ε he] with i hi he; rw [show p i= _ from dif_neg he]; exact hi
   apply aside hs ht
   · filter_upwards [s.cofinal.eventually U.proper] with i hi; rw [hp]; exact hi
   have hx : ∀ᶠ r in home, 2 ≤ H (w r):= ((Next.Rank.Station.hat_rate C.path.levels E.simpleGate).comp hz.rank).eventually_ge_atTop _
   filter_upwards [hx,hz.region] with r hr h hi
   rw [show p r= _ from dif_neg hi]; rw [pow_zero,mul_one,Nat.zero_add,pow_one] at h
   refine ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left ?_ (C.S.a_pos _).le)⟩
   have hh:= Real.log_le_sub_one_of_pos (zero_lt_two.trans_le hr); change 2+Real.log _ ≤ _; nlinarith only [hh,hr]
variable {L}
lemma moorHere [u.NeBot] (he:u ≤ f.fuse) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) :
    ∃ (L:Layout F)(s:Extraction.Sequence), Stands L U s ∧ Moored C L.level ∧ Located L ∧ StrictAnti (U.radius ∘ ⇑s):=by
   obtain ⟨s,hs⟩:= thinning U
   obtain ⟨p,hp,hQ,hR⟩:= patchM U E fx s hs
   obtain ⟨L,hl,hX,hU⟩:= installed (B:=U) he p hp (fun d _=> LinearEquiv.refl ..)
   refine ⟨L,s,⟨hU,?_⟩, hl.symm ▸ hQ,situated U L E hU P ?_ ?_ ?_,hs⟩
   · rw [hl]; exact hR
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   rw [hX]; exact Eventually.of_forall fun _=>rfl
omit E fx
variable (h:Reach C p) (hp:Reach C q) {k:ℕ}
include h
lemma tollRatio : Tendsto (fun r=> H (p r)/ρ r) home (𝓝 G.slopeConstant):=by
   have hh:= (tendsto_const_nhds (x:=C.path.levels.clock.bar)).div_atTop ageLarge
   have hx:= hh.add (tendsto_const_nhds (x:=G.slopeConstant)|>.mul h.nearby); rw [mul_one,zero_add] at hx; exact hx.congr fun r=>by rw [← mul_div_assoc,← add_div]; rfl
include E
lemma bequeath (hz:Sized C k q) (hl:Moored C p) : ∀ᶠ r in home,
   H (p r) ≤ H (q r)^2 ∧
   a (p r) / a (q r) ≤ H (q r)^(2*(k+1))∧ a (q r)/a (p r) ≤ H (q r)^4:= by
    have ht:=Gauge.slopeConstant_pos E.simpleGate
    have hx:= (tollRatio h).div (tollRatio (hz.reach ..)) ht.ne'; rw [div_self ht.ne'] at hx
    filter_upwards [hl,hz.region,hx.eventually (ge_mem_nhds one_lt_two),ageLarge.eventually_gt_atTop 0,
       ((Next.Rank.Station.hat_rate C.path.levels E.simpleGate).comp hz.rank).eventually_ge_atTop 2] with r hr hu hh hy hh'
    let P:= H (p r); let Q:= H (q r); have hQ:0<Q:=zero_lt_two.trans_le hh'; have hP:1≤P:=(C.path.levels.fits.delayed _).le
    have hL:0<Λ (q r):=zero_lt_one.trans_le (affordable C _)
    rw [Pi.div_apply,div_div_div_cancel_right₀ hy.ne'] at hh
    have hF : P ≤ Q^2 := ((div_le_iff₀ hQ).mp hh).trans (by nlinarith only [hQ,show 2≤Q from hh'])
    have hm:= C.S.a_pos (p r); have hn:= C.S.a_pos (q r)
    refine ⟨hF,(div_le_iff₀ hn).mpr ((hr.1.trans hu.2).trans ?_), (div_le_iff₀ hm).mpr ?_⟩
    · rw [mul_comm (a _),pow_mul]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL.le (by have hv:=Real.log_le_sub_one_of_pos hQ; change 2+Real.log Q≤Q^2; nlinarith only [hv,show 2≤Q from hh']) _) hn.le
    refine ((le_mul_of_one_le_right hn.le (one_le_pow₀ (affordable C _))).trans hu.1).trans (hr.2.trans ?_)
    rw [show 4=2*(2:ℕ) from rfl,pow_mul,mul_comm _ (a _)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hP) hF _) hm.le
end YM.RG17
