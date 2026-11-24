import YM.X.Scheme.Rope
import YM.X.Journey.Bare
/-!
# Stable recalibration modulo near-Jet precritical real H frame (association joins).
Any-order statement, used in FO with singular shape estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Lattice Function Filter Set Pert Pert.Position Pulse Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{d n:ℕ}
local notation "B"=> Bank F d
namespace Ribbon
open Reed
local notation "C'"=> pureBank F d
local notation "Fℕ"=>(atTop:Filter ℕ)
variable (S:Bare.Shop F){q:ℕ+}(hq:1<q.val)(hg:G.Simple)(D:Detector F d)(k:ℕ)
local notation "A"=> S.bank q k d
local notation "N"=> nested F hg S
variable {R:ℝ}(w:Haze.Floor R)
def tender (q:ℕ+)(S:Bare.Shop F)(k d:ℕ)(w:Haze.Floor R)(i:ℕ): Buffer F d:= if i=1 then -barter (q:=q) (k:=k) S w else 0
@[simp] lemma tender_zero : tender q S k d w 0=0:= by simp only [tender, if_neg Nat.zero_ne_one]
@[simp] lemma tender_one : tender q S k d w 1=-barter (q:=q) (k:=k) S w:=if_pos rfl
abbrev main (q:ℕ+)(S:Bare.Shop F)(k d:ℕ)(w:Haze.Floor R):= predMarket (tender q S k d w) (S.bank q k d)
@[simp] lemma main_zero : main q S k d w 0= S.bank q k d 0:= by rw [main,pred_zero,tender_zero,market_zero]
variable (t:Test n)(s:Pert.Position.Section F d)
private lemma outP (p: Buffer F d)(v:alma (E F d) n)(c:ℂ)(x:Fin n→ E F d):c -passV (bufferL F p) v x=c+ passV (-bufferL F p) v x:=by rw [sub_eq_add_neg]; simp only [pass_view, LinearMap.neg_apply, Finset.sum_neg_distrib, MultilinearMap.map_update_neg]
include hq
lemma steady_b(c: Pert.Position.Section F d): Tendsto (fun k=>lookie F c (main q S k d w 0)) atTop (𝓝 (lookie F c C')):= by simp_rw [main_zero]; exact S.bank_white q hq ..
include hg
lemma costs_early {r:ℝ}(hr:R<r)(hs:Curve t⊆ Pulse.Region n r)(p:Fin n→ E F d): Released (fun k=> main q S k d w 1 n t p):=by
    have he (k:ℕ):main q S k d w 1 n t p= _ := come_zero (S.bank q k d) (tender q S k d w) t p (tender_zero ..); have hx (b:Buffer F d): bufferL F (-b)=- bufferL F b:= LinearMap.ext fun _=>rfl
    simp_rw [he, tender_one]; apply Eq.mp ?_ (walks_budget S w t hq hr hg hs p); congr 1; ext1 i; rw [← member_kin,MultilinearMap.sub_apply,hx]; apply outP -- direction sub
lemma lens_ready {u: Pert.Position.Section F d}{r:ℝ}(hr:R<r)(hx:Curve u.f⊆Pulse.Region u.r r): Released (fun k=> expose F u.f (main q S k d w 1)):= Released.piR (fun _=> costs_early S hq hg w u.f hr hx _)
-- clearance of rail and an external test. avoids a single local radius beyond nearest neighbor in any comparison
lemma essential : Released (fun k=> lookie F s (predMarket (D.report (S.bank q k d)) (S.bank q k d) 1)):=by
    let H:=D.rail
    have ht:= (eventually_all.mpr (fun i:H.reached=> region_time (region_compact (H.reachedV i).f) (conf_curve _))) -- explicit binder finite nonempty compact case
    obtain ⟨r, hr, hs, hy⟩:= ((show ∀ᶠ x:ℝ in 𝓝[>] 0, x∈ Ioi (0:ℝ) from self_mem_nhdsWithin).and ((region_time (region_compact s.f) (conf_curve _)).and ht)).exists
    change r>0 at hr; obtain ⟨w⟩:= Haze.Floor.make (R:=r/2) (by linarith); let g:= main (R:=r/2) q S; have he : r/2<r:= by linarith
    have hx(s:Pert.Position.Section F d):= steady_b S hq w s; let f(k):=g k d w; have hw : Released (fun i=> D.read (f i 1)):= by choose x hx using (fun i:H.reached=> lens_ready (u:=H.reachedV i) S hq hg w he (hy i)); exact ⟨x,tendsto_pi_nhds.mpr hx⟩ -- names
    obtain ⟨C,hc⟩:= page_race D f hx _ hw (lens_ready (u:=s) S hq hg w he hs); refine ⟨C,hc.congr' ?_⟩; filter_upwards [D.patches (q:=fun k=> S.bank q k d 0) (S.bank_white q hq)] with i hi; rw [coincideH D (p:=tender q S i d w) _ (tender_zero ..) hi]
lemma full_stick : Tendsto (fun k=>lookie F s (S.uncut hg q k d 0)) atTop (𝓝 (lookie F s C')):= page_head (N d) (fun k=>S.bank q k d) (S.bank_white q hq) s
lemma full_heart : Released (fun k=> lookie F s (S.uncut hg q k d 1)):= essential S hq hg (N d) s
end Ribbon
end YM.PositionX
