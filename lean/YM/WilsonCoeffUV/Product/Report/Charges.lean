import YM.WilsonCoeffUV.Product.Report.Shapes
/-!
# Field-specific layout charges
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b m M N:ℕ}{H:Hol G}{E W V':Credit}{y δ:ℝ}
-- printed once, anchors assigned elsewhere.
structure SealR (G:Gauge) where
   h:ℕ
   F:Frame G h
   D:ℕ
   ans:SectionData F
   path:h<D
namespace SealR
variable (Q:SealR G)
abbrev Rider:=Verse Q.F
abbrev spins (A:Levels G)(Ñ:ChartRatio G)(φ:Rarity Q.D)(m i N:ℕ)(y:ℝ)(X:Q.Rider): Era G Lounge:=FirstCharge A Ñ Q.ans Q.path φ m i N y X
lemma tokenR (L:Theatre H Q.ans Q.path e E W)(φ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(v:L.V.anchor ≤ i) (p:i ≤ N): Auth Q.h (Q.spins L.V.draws L.V.paid φ m i N y X):= tokenPaid L φ X y v p
end SealR
variable {u z:ℕ}{Q:SealR G}{R:Realm G (e+1) E}
-- financing canonical stamps; same operations but room bills not same
structure PassportC (H:Hol G)(R:Realm G (e+1) E)(Q:SealR G)(W V:Credit) where
   f: ChorusLine H Q.ans Q.path e E W V
   lands:f.arch.V.draws=R.draws
   modes:f.arch.V.paid=R.paid
   depths:f.arch.V.y=R.y
   tap:f.arch.V.anchor=R.anchor
variable {t:A<B}
abbrev Terms (e:ℕ)(Q:SealR G)(A δ:ℝ)(X Y:Q.Rider):Prop:=∀ i ≤ e,∀ j,twain A δ (coeff i (X j)) (coeff i (Y j))
lemma passportHead (P:PassportC H R Q W V')(φ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(v:R.anchor≤ i)(t:i≤ N): Auth Q.h (Q.spins R.draws R.paid φ m i N y X):= by
   rw [←P.lands,←P.modes]; exact Q.tokenR P.f.arch _ _ _ (P.tap.symm ▸ v) t
lemma passportCarry (P:PassportC H R Q W V')(φ:Rarity Q.D)(X:Q.Rider)(o:CellR)(v:R.anchor≤ m)(t:m≤ i)(q:i<N):
   let S n:=locale o (Q.spins R.draws R.paid φ m n N y X); verseI R.draws R.paid i N Q.h (S (i+1))= S i:=by
    intro S
    have he:Auth Q.h (Q.spins R.draws R.paid φ m (i+1) N y X):=passportHead P _ _ _ (by omega) q
    unfold S locale; rw [← ply_verse R.draws q R.hG R.green he]; congr 1; rw [← P.lands,←P.modes]; exact priceReset P.f.arch _ _ _ (P.tap.symm ▸ v) t q
lemma surSeen (P:PassportC H R Q W V'){Z:ℝ}(v:R.anchor≤m)(t:m ≤ i)(p:i≤ b)(q:b ≤ N)(f:b≤ M) (x: Compar R.draws.S R.y m i ≤ Z) (g:0≤A)(H':R.tempC i b ≤ δ)(X Y:Q.Rider)(z:Terms e Q A δ X Y)(o i':ℕ)(u:i'≤e)(j):
   let V:= R.draws; let N' n:=polarP V R.paid Q.ans Q.path n m i
   let C:=(polarBill H Q.ans Q.path e o E W V').choose; YieldP 0 1 o (C.buy Z*A) δ ((N' N X).2 i' j) ((N' M Y).2 i' j):=by
     intro V N' C; unfold N' V; rw [←P.lands,←P.modes]; apply (polarBill H Q.ans Q.path e o E W V').choose_spec P.f _ _ b N M X Y A δ Z (P.tap.symm ▸ v) t p f q _ g _ z i' u j
     · rw [P.lands,P.depths]; exact x
     unfold tempC; rw [P.lands]; exact H'
-- Price standard: radius charge chosen to absorb y capture & profile path
lemma roads (φ:Rarity D){x y Z:ℝ}(p:φ.radius≤ Z)(v: |y|≤ Z)(t:0<x)(g:x≤1):radiusH φ x y≤3*Z:=by have h:=φ.markG; unfold radiusH; rw [abs_of_pos t]; linarith

def BaseBillP (u:ℕ)(L:Credit):Credit:= let C:= Credit.leanC; let X:= (pur 15).prodC C; let Y:= (pur 13).prodC C; ((X.powC 4).prodC (Y.powC u)).prodC L
lemma pledgeGold (T:Credit)(u:ℕ){x y Z:ℝ}(φ:Rarity D)(p:φ.radius≤ Z)(v: |y|≤ Z)(t:0<x)(g:x≤1)(h:Amplitude φ B)(ha:0 ≤ A)(k:ℕ):
    let C:=BasePrice k φ x y; let L:= BaseBillP u T; C*((1+4*radiusH φ x y)^u*(B*(T.buy Z*A)))≤ L.buy Z*(x^k)⁻¹*(B*A)∧ C*(9^u*(B*(T.buy Z*A))) ≤ L.buy Z*(x^k)⁻¹*(B*A):=by
    intro C L; have hv:=h.1; let R:=radiusH φ x y; have hR:1≤R:= fieldCap ..; have hx:=φ.markG.trans p
    let X:=(pur 15).prodC Credit.leanC; let Y:=(pur 13).prodC Credit.leanC
    have hY: 1+4*R ≤ Y.buy Z:= by unfold Y; rw [Credit.products, Credit.lean_cost,pur,Credit.buy]; norm_num; linarith [show R≤3*Z from roads _ p v t g]
    have hP:(9:ℝ)≤ Y.buy Z:=by unfold Y; rw [Credit.products,Credit.lean_cost,pur,Credit.buy]; norm_num; linarith
    have hX: 5*R≤ X.buy Z:=by unfold X; rw [Credit.products, Credit.lean_cost,pur,Credit.buy]; norm_num; linarith [show R≤3*Z from roads _ p v t g]
    have hT:0≤ T.buy Z:= zero_le_one.trans (T.purchase hx); have hh:0≤ Z:=zero_le_one.trans hx
    have hB (Q:ℝ)(p:0≤Q)(v:Q≤Y.buy Z): C*(Q^u*(B*(T.buy Z*A))) ≤ L.buy Z * (x^k)⁻¹*(B*A):= by
       rw [show L.buy Z=X.buy Z^4 * Y.buy Z^u * T.buy Z from by unfold L X Y BaseBillP; simp only [Credit.products, Credit.power]]
       refine le_trans ?_ (le_of_eq (show ((x^k)⁻¹*(X.buy Z)^4)*(Y.buy Z^u*(B*(T.buy Z*A)))= _ from by ring)); unfold C BasePrice; change (_*(5*R)^4)*_ ≤ _; gcongr
    exact ⟨hB _ (by change 0≤1+4*R; linarith) hY,hB _ (by norm_num) hP⟩

def hardCash (e u:ℕ)(E W V':Credit)(H:Hol G)(Q:SealR G):Credit:= BaseBillP u ((polarBill H Q.ans Q.path e u E W V').choose)
lemma capLife (P:PassportC H R Q W V'){Z:ℝ}(v:R.anchor≤m)(t:m ≤ i)(p:i≤ b)(q:b ≤ N)(f:b≤ M) (x: Compar R.draws.S R.y m i ≤ Z) (g:0≤A)(H':R.tempC i b ≤ δ)(X Y:Q.Rider)(z:Terms e Q A δ X Y) (Φ:Rarity Q.D)(a:Φ.radius≤ Z)(u:ℕ)(o:CellR)(φ: |y|≤ Z)(y':Amplitude Φ B):
     let A' n d:= Q.spins R.draws R.paid Φ m i n y d; let π:= paceT R.draws.S m i; let C:=(hardCash e u E W V' H Q).buy Z*(π^Q.h)⁻¹*(B*A); Fringed Q.h e u π C δ (locale o (A' N X)) (locale o (A' M Y)) ∧ ∀ L:Patch, PaidMer e u (OrbP L Φ π y o) (locale o (A' N X)) (locale o (A' M Y)) C δ:=by
    intro A' π C; have hp:N≥i:=p.trans q; have hv:P.f.arch.V.anchor≤ i:=by rw [P.tap]; exact v.trans t
    let D:=(polarBill H Q.ans Q.path e u E W V').choose; let F (n:ℕ) (U:Q.Rider):=polarP R.draws R.paid Q.ans Q.path n m i U; have he (X) (n:ℕ)(hn:i ≤ n): On Q.h (F n X):=by unfold F; rw [←P.lands,←P.modes]; exact tournure P.f.arch X hv hn
    have ht l (v':l≤e) j: YieldP 0 1 u (D.buy Z*A) δ ((F N X).2 l j) ((F M Y).2 l j):=surSeen P v t p q f x g H' X Y z u l v' _
    have heq:0<π:=pace_pos ..; have hh:π≤1:= pace_le _ t; have hx:=pledgeGold D u Φ a φ heq hh y' g Q.h; have hθ:0≤δ:= (trail_pos ..).le.trans H'
    exact ⟨(census_br (F N X) (F M Y) Φ π y (he X N hp) (he Y M (p.trans f)) o u heq hh y' ht hθ Q.h).pay hx.1,fun L i j p=> (orbFunds (F N X) (F M Y) Φ π y o u heq hh y' L ht hθ Q.h i j p).stepX hx.2 hθ⟩
end YM.WilsonCoeffUV.Mer
