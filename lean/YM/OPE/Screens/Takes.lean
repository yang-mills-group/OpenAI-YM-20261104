import YM.OPE.Screens.Salary
/-! # Cash for transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Payments
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake Rhythm.Store Rhythm Next.UVStress
open scoped Topology BigOperators Classical ContDiff
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {H l m k b N p A t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {Y:Type}{f:Filter Y}{T a c w w' : Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{P:ℝ}
    {F:Y→Loom Q} {B:Border f T Q.limit R r α} (D:Oscars B P F C)
variable {W r' D'}(L:LogPackage C W r' D')
local notation "Y!"=> C.path.levels
local notation "b!"=> (fun i t=> (F i).below t)
local notation "j!"=> (fun i t=> (F i).launch t)
local notation "β"=> C.path.levels.clock.hatBeta
local notation "μ!"=> C.S.a
local notation "τ!"=> ValueStamp f T
local notation "κ"=> Wallet f T
local notation "d!"=> (fun i t=>R i t)
local notation "a!"=> (fun i=> a i/(R i t)^d)
include D L
variable {x:Y→ℕ→ℝ}
lemma cap_fuel (h:t ≤ Q.limit)(hc:0<A)(hx:ValueStamp f T (fun i=> x i (t+1)))(hw:ValueStamp f T (fun i=> a i/w i))(d:ℕ) : Wallet f T (fun i=> a i/R i t^d*(2*stampOut C ((F i).below t) d (provision L (F i) A (x i) t*w i))):=by
    simp_rw [Tariff.quote_size]; let k i:= (F i).below t; let χ i:= provision L (F i) A (x i) t; have hp:= ((tip D h).div (costBand D L h)); let v i:= μ! (k i+1); have ht:= B.life; have hh : ValueStamp f T (fun i=> v i /R i t):=by apply hp.congr; filter_upwards [(B.ahead h).pos] with i hi; have he:= C.S.a_pos (k i+1); have hh:= C.S.a_pos ((F i).launch t); unfold v k; field_simp -- indent
    apply ((Wallet.const ht (2:ℝ)).mul (((shelfstamp D L h).div (proceeds D L h hc hx)).up.mul (hw.up.mul (hh.up.pow ht d)))).congr; filter_upwards with i; unfold v k; simp only [div_eq_mul_inv,mul_inv_rev]; ring
lemma studioPrice (h:t≤Q.limit)(hc:0<A)(hx:ValueStamp f T (fun i=> x i (t+1)))(hw:ValueStamp f T (fun i=> a i / w i))(d b q:ℕ) : Wallet f T (fun i=> a i/R i t^d*(stakes C b q/road C ((F i).below t) d (discharged L (F i) A (x i) t d*w i) q)):=by
    let v i:=C.S.a ((F i).below t); have hT:=B.life; apply ((hw.div (recipient_price D L h hc hx d)).up.mul ((Wallet.const hT (stakes C b q /C.S.a q^d)).mul ((D.loggap t h).up.pow hT d))).congr; filter_upwards with i; unfold road; simp only [div_eq_mul_inv,mul_inv_rev]; ring_nf; simp only [inv_inv]; ring
omit L
variable {G': Register G}(p': I→ G'.Token)
def priceSet (Q:Rhythm I)(V:Finset I)(p':I→ G'.Token)(R:ℕ→ℝ) : ℝ := ∏ i∈V,R (Q.age i)^(p' i).1
local notation "d'"=> (fun i=> (p' i).1)
variable {s:Finset I}
lemma mass_pos (V:Finset I): ∀ᶠ i in f,0< priceSet Q V p' (R i):=by
    filter_upwards [eventually_all.mpr (fun i:I=> (B.ahead (Q.bounded i)).pos)] with i hi using prod_pos (fun j _=>pow_pos (hi j) _)
variable (p': I→ C.book.Token)
local notation "S'"=> Highest.base_price
lemma routine {u:Y→ I→ℝ}(he:∀ j,ValueStamp f T (fun i=> u i j)) (V:Finset I) : τ! (fun i=> priceSet Q V p' (R i) / (∏ j∈V,birthClock C ((F i).launch (Q.age j)) (p' j).1 (u i j))) :=by
    unfold priceSet birthClock; simp_rw [←prod_div_distrib]; refine ValueStamp.prod B.life fun j _=>?_
    let k i:= (F i).launch (Q.age j); let h:=Q.bounded j; let α' i:= u i j; let Y' i:= μ! (k i) /R i (Q.age j); let y:= (p' j).fst; have hx := D.upper _ h
    apply (((tip D h).pow B.life (p' j).1).inv.div ((flyStamp B.life hx (p' j).1).div (he j))).congr; filter_upwards [(B.ahead h).pos] with i hi; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring_nf; simp only [inv_inv]; ring
-- namespace bug variable p' overwritten?
abbrev fuel (R:ℕ→ℝ)(H t e:ℕ):= (R t/R H)^e
lemma fuel_pos (e:ℕ)(h:t≤Q.limit)(hp:H ≤ Q.limit): ∀ᶠ i in f,0 < fuel (R i) H t e:=by filter_upwards [(B.ahead h).pos,(B.ahead hp).pos] with i hi he using pow_pos (div_pos hi he) _
lemma bonus (e:ℕ)(h:t ≤ Q.limit)(hp:H ≤ Q.limit): ValueStamp f T (fun i=> fuel (R i) H t e / Variant.widen (F i) C H t e):=by
    apply (((D.loggap H hp).div (tip D h)).pow B.life e).congr; filter_upwards [(B.ahead h).pos,(B.ahead hp).pos] with i hi ht; unfold Variant.widen fuel; rw [← div_pow]; congr 1; have h1:= C.S.a_pos ((F i).launch t); have h2:=C.S.a_pos ((F i).below H); field_simp
-- one quota access per leaf at OWN mesh.May feed with moving sequence
variable {v: Extraction.Order}{S:Table C.book}{M:DiffPlan S}{φ:Filter (ℕ×ℕ)}
local notation "Z!"=> C.path.levels.clock.hatBeta
abbrev Pad (C:Family G) (S:Table C.book)(p:I→ C.book.Token)(j:I)(m:ℕ) (φ: Filter (ℕ×ℕ))(b:ℝ) := ∃ (x:C.label (p j).1) (f:ℕ×ℕ→ C.label (p j).1), S.project (p j).1 x=S.project (p j).1 (p j).2∧ Tendsto f φ (𝓝 x)∧ ∀ᶠ i:ℕ×ℕ in φ, quota C (p j).1 m i.1 i.2 (f i) ≤ b
lemma access (p:I→ C.book.Token)(h:MatrixTicket (C:=C) S M φ): ∃ u:Y→I→ℝ,(∀ j,ValueStamp f T (fun i=> u i j))∧ ∀ᶠ i in f,∀ j, Pad C S p j ((F i).launch (Q.age j)) φ (u i j):=by
    choose q hq using (fun j=> h.inlet (p j).1 (p j).2); exact ⟨fun i j=> β (j! i (Q.age j))^q j, fun j=> (betaStamp B.life (D.upper _ (Q.bounded j))).pow B.life (q j),eventually_all.mpr fun j=> (D.upper _ (Q.bounded j)).grows.eventually (hq j)⟩
abbrev batchClock (C:Family G)(F:Loom Q)(p:I→ C.book.Token)(a:I→ℝ) (t:ℕ):= Plain.estate t (fun j=> birthClock C (F.launch (Q.age j)) (p j).1 (a j)) (Variant.owner Q t)
omit D in
lemma homeChart (j:Loom Q)(u:I→ℝ)(p:I→ C.book.Token): batchClock C j p u H= ∏ i∈ Q.focus H,birthClock C (j.launch (Q.age i)) (p i).1 (u i):=by unfold batchClock Plain.estate lineRelease; congr 1; ext i; rw [Fibers.focuses,Q.on_focus]; exact ⟨fun h=> Q.swap ((Q.seats ..).1 h), fun h=> ((Q.seats i Q.star H).2 (Q.swap h))⟩
end YM.OPE.Log.Trunk.Payments
