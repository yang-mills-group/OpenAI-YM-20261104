import YM.SignedWilsonExpansion.Vault.CrystalClear
import YM.Integration.WilsonReceivedChronologicalRosterJointDepth
/-! # Parent Ear payment casts
 These do **not infer** K-stop later. Only choose lex common stop in Body, and carry forward
 books at exactly tuned sizes. For interpolation through ancestry use common aperture `Taxer`.

 Carry `κ= K - 2+1+1` in Berth.walls without casting all fields in dependent statements.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3000
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Integration.Election.VaultM.Cordial.Fits
open Function Finset Set Filter MeasureTheory Lattice RG Wilson Source Labels Marker Multi
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open OriginalMarkedSourceComet StressFlux.Matching Extraction Next.UVStress
open SignedWilsonExpansion SignedWilsonExpansion.Homes HeartT HeartT.Spritz SignedWilsonExpansion.StageG
open WilsonReceivedChronologicalRosterJointDepth (level precision offset)
open WilsonReceivedChronologicalRosterRanks (crop restored)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalMaterialSites (physical)
open WilsonIndependentConditionedDenseFilmBank (upper)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonIndependentConditionedDenseFilmTerminal (output)
open Liner InkP Pane SignedWilsonExpansion.Commission Cells Pert.Asymptotics SignedWilsonExpansion.Fire
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Xa MarqueQ Precision MarqueQ.Crops
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} (R : Run G) {n j₀:ℕ} {N per f vc v c P first pwr b t z K o:ℕ} {d D:Fin n→ℕ}
variable {fk:f≤j₀+1+1}{ck:c≤j₀+1+1}{cut:j₀+1+1≤N}{B:ℝ} {F:Filed R d ( j₀+1+1 )} {A:Panel R d N per f ( j₀+1+1 ) fk cut t pwr b B}
local notation "C₀" => R.family
local notation "ZK" => j₀+1+1
local notation "w₀" => votes R d (N:=N) (per:=per) F A.names A.turn
local notation "rK" => regulatorRun C₀ N per
local notation "slides" => Finset ( Fin n )
abbrev CastInvoice (d D:Fin n→ℕ)(pt: Fin n→ Chamber) {K v c f:ℕ}(h:f≤K)(hk: c ≤ K ) (b u e w:ℕ)(B:ℝ)(per:ℕ): Prop:= ∀ N:ℕ,∀HN: K≤N,∀ (x:Fin n→ Cover),Ballots.rolls (C₀).S (location ((C₀).S) f K per∘x) hk=0→
     ∀ t s:ℕ,∀ A:Filed R d K,∀ F:Panel R d N per f K h HN t w s B,∀ X Y:(i:Fin n)→( C₀ ).label (d i),Pane R A F x X Y→∀ z:Finset (Fin n),
     let V:=regulatorRun C₀ N per v; let out:= calcT (↑V) u (InkP.valued R d ( D:=D ) pt N per v K c Y ( location ((C₀).S) f K per∘x ) z );
     ‖born₀ C₀ d x Y f N per b K z-out‖≤ V^e ∧ ‖born₀ C₀ d x Y f N per v K z - out‖≤ V^e
structure Train (d: Fin n→ℕ) (D: Fin n→ℕ) (pt: Fin n→ Chamber)(j₀ first t f v b e c pwr per:ℕ)(B:ℝ):Prop where
    seats : f ≤ j₀+1+1
    older : b ≤ first+1
    size : first+1 ≤ c
    duration : c ≤ j₀+1+1
    correct : v=first+1
-- no data all prop; horizon polynomial degree = t
    rows : ∀ N:ℕ,∀ live : j₀+1+1≤N, ∃P:ℕ,∃V : Realm G ((WilsonReceivedChronologicalFixedReserve.terms d (fun _=>0) P).order+1) Credit.leanC,∃draw : V.draws=R.family.path.levels,
     ∀ s t₀:ℕ, ∀ A: Panel R d N per f (j₀+1+1) seats live s pwr t₀ B, (∀i,physical R (placed R seats A.loc) duration i=0)→ ∀F:Filed R d ( j₀+1+1 ),A.slot=F.station→A.axis=F.A N per→∀S:(Stock.census (Fin n)).Mode,
     let y:= votes R d (N:=N) (per:=per) F A.names A.turn; let word:= upper R d (N:=N) seats A.loc y S; let out:= output (R:=R) (d:=d) (P:=P) (N:=N) (j:=j₀) (per:=per) (first:=first) (V:=V) (draw:=draw) (lens:=D) (pt:=pt) (fine:=seats) (site:=A.loc) (votes:=y) (mask:=S) c t;
     ‖actualTransport C₀ (N:=N) word (older.trans (size.trans duration)) 1-out‖≤ (regulatorRun C₀ N per (first+1) )^e ∧ ‖actualTransport C₀ (N:=N) word (size.trans duration) 1 - out‖≤ (regulatorRun C₀ N per (first+1))^e
variable {u e w b j K a q t₀:ℕ}{pt: Fin n→Chamber}
lemma Train.book (T:Train R d D pt j first t f v b e c w per B) (h:j+1+1=K)(hu:q≤e)
   (hb:∀N≥ K,0≤regulatorRun C₀ N per v ∧ regulatorRun C₀ N per v≤1) : CastInvoice (v:=v) R d D pt (T.seats.trans h.le) (T.duration.trans h.le) b t q w B per:=by
    have he:= T.correct; subst K v
    intro N hn x hx s t' A F X Y P₀ S
    let V:=regulatorRun C₀ N per (first+1); let out:=calcT (↑V) t (InkP.valued R d ( D:=D ) pt N per (first+1) (j+1+1) c Y ( location ((C₀).S) f (j+1+1) per∘x ) S );
    obtain ⟨p,W,draw,hit⟩:= T.rows N hn; have hw:= hit s t' F ( rooted R P₀ hx ) A P₀.stations P₀.home (capM S)
    let hs:= seeded (first:=first) (D:=D) R P₀ S draw pt c t; have hv:V^e ≤ V^q:= pow_le_pow_of_le_one (hb N hn).1 (hb N hn).2 hu; let hm:= literal R P₀ S ( T.size.trans T.duration ); change ‖_ -out‖≤V^q ∧ ‖_ -out‖≤V^q; unfold out; rw [hm,literal R P₀ S (T.older.trans ( T.size.trans T.duration )),hs]; exact ⟨hw.1.trans hv,hw.2.trans hv ⟩
open Till SignedWilsonExpansion.Vault Camera
variable {axis:Axis}{S:Plans axis}{cap:ℕ}
section
-- Tariffs for any Want* list. use oriented.home.same turn
variable (S cap)
abbrev DOB (_d:ℕ) (p q:ℕ )(w:Draft G cap S):= WilsonReceivedChronologicalRosterJointDepth.precision (Draft.bill) stampK (fun _=>p) (fun _=>q) w
abbrev tax (_d:ℕ)(p q:ℕ)(w:Draft G cap S):= crop ( Draft.bill w ) ( restored ( Draft.bill w ) p ( DOB S cap _d p q w ) )
abbrev levelX (a b _p:ℕ):= 4*WilsonReceivedChronologicalRosterJointDepth.level (Draft.bill (G:=G) (D:=cap) (B:=S)) (stampK (G:=G) (D:=cap) (S:=S)) (fun _=>a) (fun _=>b)
variable {x:Draft G cap S}
lemma tax_pos (d p q:ℕ) (w:Draft G cap S) : q ≤ DOB S cap d p q w ∧ DOB S cap d p q w≤ tax S cap d p q w :=by
   refine ⟨(WilsonReceivedChronologicalRosterJointDepth.original Draft.bill stampK (fun _=>p) (fun _=>q) w ).1,?_⟩; exact le_trans (show _ ≤ restored (Draft.bill w) p (DOB S cap d p q w) from le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)) (Nat.le_add_right ..)
lemma housed (d p q:ℕ)(H: 0<cap): q ≤ levelX (G:=G) S cap p q d:=by
    haveI : Nonempty (Draft G cap S):= ⟨ Draft.first H false ⟩; let x:Draft G cap S:=Classical.arbitrary _; let X:= WilsonReceivedChronologicalRosterJointDepth.level (Draft.bill (G:=G) (D:=cap) (B:=S)) stampK (fun _=>p) (fun _=>q)
    have ht:= ( tax_pos S cap d p q x).1; have hu:DOB S cap d p q x≤ X := Nat.sub_le ..; change q≤ 4*X; omega
lemma uniformTax (d p q:ℕ)(w w':Draft G cap S)(h:progC w=progC w'): tax S cap d p q w= tax S cap d p q w':=by
   let X:= WilsonReceivedChronologicalRosterJointDepth.level (Draft.bill (G:=G) (D:=cap) (B:=S)) stampK (fun _=>p) (fun _=>q); let Y:= (fun t:listT cap S=> WilsonReceivedChronologicalRosterRanks.crop (t.1.val+1) ( restored (t.1.val+1) p ( X-WilsonReceivedChronologicalRosterJointDepth.offset t.2 p ) ) ); change Y (progC w)=Y (progC w'); rw [h]
end
end YM.Integration.Election.VaultM.Cordial.Fits
