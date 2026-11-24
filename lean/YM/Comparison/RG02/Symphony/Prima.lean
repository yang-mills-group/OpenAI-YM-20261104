import YM.Comparison.RG02.Symphony.Grown
import YM.Comparison.RG02.Baseline.Floral
/-!
# Local on the *same* History: pay `ω_e` at the correct coupling
 Spare can be pulled at Oasis (on the real construction). Next, `Front` consumes symbols
 offered from the cover-compatible mesh Fk ranks, then uses those symbols to set and/or certify the Caliber. This is for one step, formal primitive inputs shared across period as declared.
 Need offer analytical rank-two symbols THROUGH r on this actual Mesh for higher k; no receipt
 on arbitrary alternative regulator or divergent phase removed. Need Fk inputs chosen independent
 of later report order (apply on projection). For the actual β reset, Spare pays the width; the displacement
 we know delivers the shift alpha to **THIS** accuracy only, so consumers typically still need
 upgrade (for that and for higher-order terms). `Construction` is still the chosen C (not the `b` path offsets
 used inside proof) hence uses same Field and calibration. All directions here on unphased RG path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
open UVNext.CouplingReset
structure Spare {P: History G}(L:Bulk.Chain P) where
  currency: MapPrices
  planned : L.horizon.Suffices currency
  rails N i c : i≤N → Bid.Sworn (L.horizon.H N i) c G
  refund : ResetPrices
  reward N i p : i<N→|(P.rep N p i).beta - (P.rep N p (i+1)).beta -L.kin.alpha N i| ≤ width P.levels i refund

namespace Spare
-- pass this **bound pair** from ONE constructor, don't choose arbitrary different Y for readers.
variable (T:Family G)(hG:G.Simple)(H: UVExtension.Oasis.Floral T (hG:=hG))
include H
theorem at_Construction : ∃ L:Bulk.Chain T.path, Nonempty (Spare L):= by
   obtain ⟨M,D,A,R,S,U,t,K,w,Q,T,-,rfl,hO,-⟩:=H
   let L : Bulk.Chain (A.B.bake.make (S.realBeat 0)) := ⟨M.p,D,A.post,A.B.M,M.O,M.oga,A.B.kin,A.B.support,fun N p m hp=> (hO.actual m p N hp 0 (by rw [abs_zero]; exact hO.open_at)).1,fun N p m hp=> (hO.actual m p N hp 0 (by rw [abs_zero]; exact hO.open_at)).2.1⟩
   exact ⟨L, M.K, A.B.plan, R.pledging.conducts.full, R.post, fun N i p h=> ((S.housing N p (UVExtension.Spire.Uses.centerP _) i h).2.1)⟩
end Spare

variable {P : RG.History G} {V:Type}[Fintype V][DecidableEq V]{R:Census V}
namespace Front
open LocalScript (winter)
variable (L:Bulk.Chain P) (N m r:ℕ) (h:m<N) (k i:ℕ)
    (F: ∀ i,Forest (P.levels.clock.op m i).ratio) (u:∀ i,(P.levels.clock.op m i).Choices)(W: ∀ i,Bulk.Colors R G (P.S.side (m+1) i))(C:Caliber)
    (S:Spare L)
    (hr:2≤r)(hW:∀ i,(W i).Standard)
set_option quotPrecheck false
local notation "ν"=> Project P m
local notation "α"=> L.kin.alpha N m
local notation "L0"=> fun i=> ground (L.step N m i h) (F i) (u i) (W i)
local notation "ξ"=> Roster.series L N m r h F u W
local notation "Ξ"=> Grown.inverse ξ C r
variable (a:G.ColorIndex)(hG:G.Simple)
structure Require : Prop where
    honest : ∀i,(W i).Standard
    calm : ∀i, Mirror.Calm (W i)
    ports (i:ℕ)(s:Signed)(c: Site (P.S.side m i))(x:ℝ): (W i).vac x ∘ pull s ((P.levels.clock.op m i).ratio.embed c)=(W i).vac x
variable (Y:Require m W)
variable (b:ℕ→SpecK G)(hq:∀ k≤r,Offer (b k) (Roster.series L N m r h F u W k))(hp: Grown.Canon C (Roster.series L N m r h F u W) r)
include Y hr h
omit Y
include hW S
lemma low : Offer (Roster.core L N m 0) (ξ 0) ∧ Offer (Roster.core L N m 2) (ξ 2) ∧ probe₂ (Roster.core L N m 0) a=1 ∧ probe₂ (Roster.core L N m 2) a=Complex.ofReal (α) := by
   exact ⟨Roster.zeroth L N m r h S.planned (fun i=>S.rails N m (ν i) h.le) F u W,Roster.second L N m r h S.planned (fun i=>S.rails N m (ν i) h.le) F u W hr hW,Roster.pays L N m h S.planned a,Roster.keeps L N m h S.planned a⟩
include hp
include a in
lemma certifies : C.measure 2=L.kin.alpha N m:= by
   obtain ⟨s,hs,hq⟩:= hp.paid 2 hr; obtain ⟨-,he,-,h⟩:= low L N m r h F u W S hr hW a; exact Complex.ofReal_inj.mp ((hq a).symm.trans ((hs.unique_price a (climbs P m) he).trans h))
-- low DOES authorize actual Caliber formal fee through this order, regardless of higher inputs. Not inheritance precision.
include hG
omit hp
private lemma below (k:ℕ) (_:k≤r)(hv:k≤2): Offer (Roster.core L N m k) (ξ k) := Roster.supply L N m r h k S.planned (fun i=>S.rails N m (ν i) h.le) F u W hr hW hG hv
include a
-- canonical through requested low at r≥2; set measure=0 above in low-only Caliber
lemma lowest : Grown.Canon (Grown.prescribes (Roster.core L N m) a) ξ 2 := by
   constructor
   intro k he; refine ⟨_, below L N m r h F u W S hr hW hG k (he.trans hr) he,?_⟩; intro z; interval_cases k <;> dsimp only [Grown.prescribes]
   · rw [if_pos rfl , show Roster.core L N m 0=_ from (show _=kineticSymbol G (L.horizon.H N m).metric from rfl), Roster.pays L N m h S.planned]; simp
   · rw [if_neg (by omega), show Roster.core L N m 1=0 from rfl,zero_probe,zero_probe]; simp
   rw [if_neg (by omega), show Roster.core L N m 2=Seed.second (L.horizon.H N m) (L.kin.path N m) (α) from rfl, Roster.keeps L N m h S.planned,Roster.keeps L N m h S.planned]; rfl
include hp
lemma first : C.measure 1=0:= by
    let U:= Grown.prescribes (Roster.core L N m) a
    have ht : C.measure 1=U.measure 1:= Grown.unique_coeff ξ 2 1 U a (climbs P m) (lowest L N m r h F u W S hr hW a hG) (by omega) (d:=C) ⟨fun k he=>hp.paid k (he.trans hr)⟩
    rw [ht]; unfold U Grown.prescribes; dsimp only; rw [if_neg (by omega),show Roster.core L N m 1=0 from rfl,zero_probe]; rfl
omit hW S hp hr a hG
include Y
lemma turns : ∀k≤r,∀ i s,(Roster.series L N m r h F u W k) i ∘ shifts s 0=(ξ k) i := fun k _ i s=> Pole.season _ (P.levels.budget m) _ _ s 0 r ((Y.honest i).1) (Y.ports i s 0) k
local notation "T"=> (fun i:ℕ=> (↑i+2:ℤ))
omit Y in
lemma ranks : ∀i,Charge r (fun i:ℕ=> (↑i+2:ℤ)) (fun k=> (ξ k) i):= fun i=> LocalScript.rank (L.step N m i h) (F i) (u i) (W i) r
lemma known : ∀ i, Sheet r (fun k=> (ξ k) i):= fun i=> Symmetry.Orbit.bed _ (P.levels.budget m) _ _ _ r ((Y.honest i).1)
include S hr hG hq a
lemma assigns : Grown.Canon (Grown.prescribes b a) ξ r:= Grown.making ξ r b (ranks L N m r h F u W) hG a hq (known L N m r h F u W Y) (turns L N m r h F u W Y) (climbs P m) (by rw [(hq 0 (Nat.zero_le _)).unique_price a (climbs P m) (low L N m r h F u W S hr Y.honest a|>.1)]; exact (low L N m r h F u W S hr Y.honest a).2.2.1)
omit S hr hG hq
include hp
lemma evenK : C.EvenK r:= by
   intro k he hO; obtain ⟨s,hu,hc⟩:= hp.paid k he; have hv:k≠0:= fun hk=> Nat.not_odd_zero (hk ▸ hO); have hp : probe₂ s a=0:= (hu.unique_price a (climbs P m) (Offer.none ?_)).trans (zero_probe a)
   swap
   · intro i; let x:= ξ k i; let y:= Clarity.reads (p:=x) (smooth_ground (L.step N m i h) _ _ (W i) r k|>.contDiffAt); have h0(i:ℕ): iteratedFDeriv ℝ 2 (ground (L.step N m i h) (F i) (u i) (W i) r k) 0=0:=by rw [show ground _ _ _ _ r k=(fun x=> detail _ R.quiet k) from funext fun x=> by unfold ground; rw [if_neg hv, add_zero]]; exact Valence.Parity.lean_loop (L.step N m i h) _ _ _ r ((Y.honest i).1) k (Y.calm i) hO
     apply pairing_ext; intro v z; rw [y v z,show iteratedFDeriv ℝ 2 x 0=0 from h0 i,Matrix.zero_mulVec,dotProduct_zero]; simp
   exact Complex.ofReal_eq_zero.mp ((hc a).symm.trans hp)
include hG hq
lemma read (hk:k≤r): Offer (Grown.forecast C r b k) ((Grown.inverse ξ C r) k) ∧ Signature G true (Grown.forecast C r b k) ∧ (probe₂ (Grown.forecast C r b k) a= if k=0 then 1 else 0) ∧ ( k≠0 → Signature.Short (Grown.forecast C r b k) 4):= by
    have he:= ranks L N m r h F u W; have hb:Monotone (fun i:ℕ=> (↑i+2:ℤ)):= fun i j h=> by change (i:ℤ)+_≤ j+2; omega
    have ht:=climbs P m; have hh:=known L N m r h F u W Y; have hx:= turns L N m r h F u W Y; have h':= Grown.provides ξ r k C b he hb hq hk; exact ⟨h',h'.signature ht (Grown.after ξ r k C he hb hG hh hx hk),Grown.response ξ r k C b a hq ht hp hk, Grown.vanished ξ r k C b he hb hG a hq hh hx ht hp hk⟩
end Front
end YM.Comparison.RG02.Symphony
