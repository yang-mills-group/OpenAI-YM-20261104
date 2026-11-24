import YM.GapsContact.Earn.Trek
/-!
# Wind from stencil out to the graph projector, keep higher costs

Projecting before interpolating, and controlling ALL mismatching projections. Pay off-diagonal
log budget and normalized Gram price with any polynomial power chosen later. Do not ask
for relative logarithms of the field cost difference until it is proved. No contour compared
on matching with a query frozen (fields themselves may depend on clock position,
then the analysis is applied uniformly). Use near-shell estimates for dynamical matrix on X only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Set Function Filter MeasureTheory Analysis Spec Table Extraction Lattice RG Wilson
open Frontier6 Frontier6.Tale Frontier6.Road Ascent Power Trace Trace.Terrace Trace.Pilot
open OPE OPE.Log
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {C: Family G} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)
variable {I V J:Type}[Fintype I][Fintype J] {T g R t y: V →ℝ}
variable {l:Filter V}{hG:G.Simple}{A:EveryPhase.Almanac F} {d D:ℕ}{o C':V→ℝ}
variable {ε a b c:ℝ}{w: V→ Spelling S}
variable (hT:Tendsto T l atTop)
variable {𝓛:Ultrafilter (ℕ×ℕ)}{Z:Trace.Terrace.Arch C}{Q:(Climb.Bel C.book).Hierarchy}
universe u
variable (H:Roll.{u} F hG A) (hU:Bliss F 𝓛 Z Q)

local notation "T0" => F.room.kernel
local notation "Z₀" => fun _ : Unit=> (0:E4)

-- for bills that pay every input separately and balance derivatives after prices. permits unbounded growth of other labels.
abbrev Pass (X: V → Spelling S) (v:V→ S.Field d)(p:V→ E4) (k:V) : Spelling S:= X k-letter S (p k) ⟨d,v k⟩
-- compare against EVERY normalized bell (varying reads), derive true wind price
lemma cost_fraction (d:ℕ)(t:ℝ)(x:S.Field d) : cost F d t ((cost F d t x)⁻¹ • x) ≤ 1:=by
   rw [paid_coin,chip_real, Real.norm_of_nonneg (inv_nonneg.mpr (Ascent.cost_pos ..)), ← paid_coin F]; by_cases h:cost F d t x=0 <;> simp [h]
include H
lemma weight_response (d:ℕ)(x:S.Field d)(t:ℝ)(ht:0<t)(he:x≠0)(_o:E4) :
    Power.bond (F.room.kernel) d t x ((cost F d t x)⁻¹ • x)= cost F d t x := by
   rw [map_smul,← bond_root _ ht,← paid_coin F]; let y:=cost F d t x; have hp:0<y:= all_good F H t ht d x he; change y⁻¹*y^2 = y; field_simp
-- valuation r% . No norm assumption on projections from stall needed!
lemma duel_price (t:V→ℝ)(r:V→ E4)(ht:∀ᶠ i in l,0<t i) (X:V→ Spelling S) {a:ℝ} {Y:V→ S.Field d} (h:∀ x:V→ S.Field d,(∀ᶠ i in l, cost F d (t i) (x i) ≤ 1) → RateLE l T (fun i=> peal F none (Pass X Y r i * bellframe F (t i) (r i) (x i))) a) : RateLE l T (fun i=> cost F d (t i) (lookup F d (r i) (t i) (X i)-Y i)) a:=by
   let V' i:= lookup F d (r i) (t i) (X i)-Y i; let c i:=cost F d (t i) (V' i); let y i:= (c i)⁻¹ • (V' i);
   apply (h y (Eventually.of_forall fun _=>cost_fraction ..)).transfer; filter_upwards [ht] with i hi
   have hw:= all_good F H (t i) hi d; by_cases he: V' i=0
   · change ‖cost F d (t i) (V' i)‖ ≤ _; rw [he,cost_zero,norm_zero]; exact norm_nonneg _
   have hv:= weight_response F H d (V' i) (t i) hi he (r i)
   change ‖c i‖ ≤ _; rw [Real.norm_of_nonneg (Ascent.cost_pos ..|>.trans_eq (by rfl)), ← show Power.bond T0 _ _ _ (y i)= c i from hv]; unfold V'; rw [← graph_one F hi hw (r i) (Y i), ← graph_sub F hi hw (r i)] -- y i might unfold not desired
   rw [graphCore F hi hw,snapshot_read]; exact Complex.re_le_norm _

variable {K:V→ℕ}
local notation "n'"=> Fintype.card J
variable {j k m q:V→ℕ}{x:V→ I→ Cover}{s:V→ StateIndex F}
variable {Y: V→ J→ E4}{d':J→ℕ}{p: V→ I→ S.Tag}
variable (r:∀ i:J,V→ S.Field (d' i)){z:V→ S.Field d}{W:J→ℝ}
local notation "α!"=> C.S.a
local notation "τ!"=> C.S.gridPoint
local notation "Ξ'"=> fun i=> assembly S (C.S.gridPoint (j i) ∘ x i) (p i)
local notation "L'" => ((d:ℝ)+1)*(3*ε)
local notation "O'" => (∑ i:J, (((d' i:ℝ)+1)*(3*ε)+W i))
local notation "ω" => (∑ i:J,W i)

variable (hK:∀ᶠ i in l,Shelf (g i) (R i) (t i))
variable (hp:Ridge l T g)
variable (hk:RateIs l T (fun i=>t i/C.S.a (q i)) ε) (hs:∀ᶠ i in l, Screen (C.S.gridPoint (j i)∘x i)) (he:∀ᶠ i in l,VisitS (g i) (R i) (C.S.gridPoint (j i)∘x i) 0) (hJ:∀ᶠ i in l,q i ≤ j i)
variable (hF:Org.Grill C f)(hS: ∀ᶠ i in l,Stall (C:=C) 𝓛 S (q i) (m i) (j i) (o i) (C' i) d (x i) (p i) (z i))(ho:RateLE l T o a)(hε:0<ε)
include hp hK hT H
omit H in
lemma ridgeT : Ridge l T t := hp.above hT (shelf_down hK) (hK.mono fun _ hi=>hi.stop)

include hU hk hs he hJ hF hS ho hε
lemma bell_price : RateLE l T (fun i=>cost F d (t i) (lookup F d 0 (t i) (Ξ' i)- z i)) (a+ ((d:ℝ)+1)*(3*ε)) :=by
   have hp:= ridgeT hT hK hp; let y i:=fun _ : Unit=> dial (t i) 0
   refine duel_price F H t (fun _:V=> (0:E4)) hp.pos (Ξ') ?_
   intro x' hx; let Y(i:V):= flipField F d (x' i); have ht': RateLE l T (fun i=>cost F d (t i) (Y i)) 0:=by
       obtain ⟨B,hB,hV⟩:= cash_spin F H d; refine RateLE.absBound B hT ?_; filter_upwards [hp.soon,hx] with i hi he; rw [Real.norm_of_nonneg (Ascent.cost_pos ..)]; exact (hV (t i) hi (x' i)).trans (mul_le_of_le_one_right (zero_le_one.trans hB) he)
   have hG : ∀ᶠ i in l, Balcony (g i) (t i) (t i) (y i) 0 ∧ Injective (beside (τ! (j i) ∘ x i) (y i)):=by
        filter_upwards [hK,hp.pos,he] with i hi hj hk; have hp:=dial_rack 0 hj (hi.fit.trans hi.tie.2); exact ⟨hp,hp.join_live hk hi⟩
   have h:= islands F (V:=V) H hU hT hp hp hk hε (Eventually.of_forall fun i=>le_refl _) (k:=fun _=>none) (e:=fun _ : Unit=>d) hF hs hJ hS ho y (fun _:Unit=> Y) (fun _=>0) hG (fun _=>ht') -- argument order
   simpa only [Pass, Fintype.sum_unique,add_zero, spendsWord,assembly,Fintype.prod_unique] using! h

omit hk hs he hJ hF hS ho hε hU
lemma raw_singlePrice {a:ℝ}{x:V→ S.Field d} (r:∀ j:J,V→ S.Field (d' j))(v:V→ E4)
    (hV:∀ᶠ i in l,Balcony (g i) (y i) (t i) (Y i) (v i))(hY:RateLE l T (fun i=>cost F d (t i) (x i)) a) (hr:∀ j:J,RateLE l T (fun i=> cost F (d' j) (y i) (r j i)) (W j)) (s:V→ StateIndex F) : RateLE l T (fun i=>peal F (s i) (letter S (v i) ⟨d,x i⟩ * spendsWord (S:=S) (Y i) d' (fun j=>r j i))) (a+(∑ j,W j)) :=by
   obtain ⟨B,m,hB,h⟩:= raw_letter F H d' d; have hz:= hp.care.pow m hT; let Y' i:= fun j=>cost F (d' j) (y i) (r j i); have hy:= RateLE.prod (S:=Finset.univ) (f:=fun j i=> Y' i j) hT fun j _=>hr j
   exact ((((((RateLE.const B hT).mul hz).mul hY).mul hy).mono (by simp))).of_norm_le ((hK.and hV).mono fun i ⟨hh,hV⟩=> h _ _ _ _ _ _ _ _ hh.stop hh.credit hV (fun j=>rfl))

include hU hk hs he hJ hF hS ho hε
lemma windPrice {s:V→ StateIndex F}
    (hB:∀ᶠ i in l,Balcony (g i) (y i) (t i) (Y i) 0)(hW:∀ j,RateLE l T (fun i=>cost F (d' j) (y i) (r j i)) (W j)) : RateLE l T (fun i=> let X:= Ξ' i; peal F (s i) ((X-letter S 0 ⟨d,lookup F d 0 (t i) X⟩)*spendsWord (S:=S) (Y i) d' (fun j=> r j i))) (a + O' + L'):=by
   let z₀(i):= lookup F d 0 (t i) (Ξ' i)- z i
   have h:= bell_price F (z:=z) hT H hU hK hp hk hs he hJ hF hS ho hε; have hP:= raw_singlePrice F (x:=z₀) hT H hK hp r (fun _=>0) hB h hW s
   have hh : ∀ᶠ i in l, y i ≤ t i:= hB.mono fun _ hi=>hi.horizon
   have hv:= ridgeT hT hK hp
   have h₁:= islands F H hU hT hv (hp.above hT (hB.mono fun _ hi=>hi.spot) ((hh.and (shelf_upper hK)).mono fun i hi=> hi.1.trans hi.2.2)) hk hε hh s d' hF hs hJ hS ho (Y) r W ((hB.and (hK.and he)).mono (fun i ⟨h₁,h₂,h₃⟩=> ⟨h₁,h₁.join_live h₃ h₂⟩)) hW -- fix >
   have hv':(∑ i:J,W i) ≤ O':= Finset.sum_le_sum fun i _=> le_add_of_nonneg_left (by positivity)
   have heL : 0 ≤ L':=by positivity
   apply (((h₁.mono (le_add_of_nonneg_right heL)).sub (hP.mono (by linarith only [hv'])) hT)).congr; filter_upwards with i; let x:= Ξ' i; let y:= spendsWord (S:=S) (Y i) d' (fun j=> r j i); change peal F (s i) ((x-_) * y)- peal _ (s i) (letter S 0 ⟨d,z₀ i⟩ *y)= peal _ _ ((x-_) * y); simp only [sub_mul,map_sub, peal, ← Tale.reads F, z₀]; abel
end YM.GapsContact.Seams
