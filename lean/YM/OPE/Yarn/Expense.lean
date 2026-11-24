import YM.OPE.Yarn.Duplicates
/-!
# Cumulative invoices at each event, including paths needing later recoveries
Keep quantitative accounting as cheap widths give polynomial in *global clock*
down to finest descendant. No propagation price strictly beyond these products. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J U:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
variable {L:Fibers I J} {k j m : U→ℕ}{u:U→I→Pod}{v:U→J→Pod}{α a b:ℝ}{t l p N:ℕ}{T:U→ℝ}
    {φ:Ultrafilter U} {d:Filter U} {K:Bool} {x y:U→ℝ}
    {c w:U→I→ℝ}{e s:I→U→ℝ}
include H
lemma pitch_bill (hc:Tendsto T d atTop)(hk:Height C.S d T k b): Coins d T (fun i=>soar C (k i)):= by
    have he:Coins d T (fun i=>1+(C.path.levels.params (k i-1)).columns) := by
       refine Coins.by_le ((Bill.const _ hc).add (columns_p hc H.cuts.toPackage.toTableTickets (prec hk)|>.up) hc) (Eventually.of_forall fun i=>?_) ; exact (le_add_of_nonneg_right (zero_le_one.trans ((C.path.levels.params _).columns_ge))).trans (Real.le_norm_self _)
    exact Coins.div (fly_coins hc hk 0) (Coins.mul (Coins.mul (Bi.const 256 (by norm_num) hc) he) (hat_price hc hk))
lemma roam_bill (hc:Tendsto T d atTop)(h:Height C.S d T k b) (he:Height C.S d T j a)(hp:K=false→Bi d T (C.S.a ∘ k) (C.S.a ∘ j)):Coins d T (fun i=>fee C (j i) (k i) K):=by
    cases K; exact price_coin hc he (hp rfl) (Bi.const _ (by norm_num) hc); exact pitch_bill H hc h
abbrev face {α β : Type*}(L₀:Fibers α β)[Fintype α][DecidableEq β](F:α→ℝ)(x:β):= ∏ i∈L₀.contents x, F i
lemma ripe_bill (E : ∀ᶠ i in (φ:Filter U),∃ p,∃ o:I→∀ k:ℕ, Site (C.side k p), Event L C o r (j i) (k i) (m i) (radiusCost C t (j i)) K (u i) (v i))
    (hx:Tendsto T φ atTop)(hj:Height C.S φ T j a)(hk:Height C.S φ T k b)(ht:∀ᶠ i in (φ:Filter U),j i<k i)(hw:∀ᶠ i in (φ:Filter U), ∀ k,0<w i k)
    (he:K=false→Bi φ T (C.S.a ∘ k) (C.S.a ∘ j))(h:∀ i:I,Bi φ T (fun j=>w j i) (e i))(hl:0<l)(x:J): Bi φ T (fun i=>promotion C (u i) (v i) (w i) (j i) (k i) l (radiusCost C t (j i)) K L x) (fun i=>face L (fun j=>e j i) x):=by
    let f i:= fee C (j i) (k i) K; let l' i:= license C.path δ l (radiusCost C t (j i)) (j i)
    have hp : Coins φ T f:= roam_bill H hx hk hj he; have hη:= near_coins hx hj; have hC:Coins φ T l' := license_polynomial hx hj t H.cuts hl; by_cases hE : ∀ᶠ i in (φ : Filter U), v i x=none
    · let v' k i:= (if u i k=none then f i else η (j i)); let X k i:= l' i*(v' k i*w i k); refine (Bi.prod (s:=L.contents x) (f:=X) (g:=e) hx (fun k hk=>?_)).congr ?_ (EventuallyEq.refl ..)
      · have hk':Coins (φ:Filter U) T (v' k) := by by_cases he :∀ᶠ i in (φ:Filter U),u i k=none; exact hp.congr (he.mono fun i hi=>(if_pos hi).symm) (EventuallyEq.refl ..); rw [← Ultrafilter.eventually_not] at he; exact hη.congr (he.mono fun i hi=>(if_neg hi).symm) (EventuallyEq.refl ..)
        unfold X; simpa only [one_mul] using Bi.mul hC (Bi.mul hk' (h k))
      filter_upwards [E,hE,hw,ht] with i ⟨p,o,H'⟩ hi hx he; unfold promotion; rw [if_pos hi]; symm; exact prod_congr rfl fun k hh=> congr_arg (l' i *·) (H'.invoice H K he L k (hx k) (((L.focuses ..).1 hh).symm ▸ hi))
    rw [← Ultrafilter.eventually_not] at hE; unfold promotion
    have hs:L.Only x:= by obtain ⟨i,⟨p,o,h'⟩,he⟩:=(E.and hE).exists; obtain ⟨k,hv⟩:= Option.ne_none_iff_exists'.mp he; exact (h'.collar x k hv).1
    refine (Bi.mul (Coins.mul hC hη) (h (L.twig x))).congr (hE.mono fun i hi=>(if_neg hi).symm) (Eventually.of_forall fun i=>?_); unfold face; rw [show L.contents x=_ from hs]; simp only [Finset.prod_singleton,one_mul]
-- first event from cutoff N≥ somewhat high first; finance separately starting only protected. Alternative insert `Prelude` stop K' above all and keep all in place without event. Then Bank.Bi ordinary.Time.Non-emptiness.
end YM.OPE.Yarn

