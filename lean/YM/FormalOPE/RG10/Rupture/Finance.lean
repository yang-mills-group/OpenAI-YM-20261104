import YM.FormalOPE.RG10.Rupture.Salted
/-! # Funded Two from oriented Episode (OR without vector-field matching),
 input rank and valuation separately. Power-law from any Tier, e.g. pure exponential
 weights everywhere in a common zoom/frame and phase. Coherent over truncated widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route HStein Tier GaugeGear Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J X:Type} [Fintype J] [Fintype I] [DecidableEq I]
variable (q:I→X)(v:B→X) (T:Tape X) (F:Tier) (e:Episode I B J)
variable {q v T F e} (O A E:Lens T){C L:ℝ} {d r i s t:ℕ}
variable (HO : Inventory e (tall F (d+1)) q v T C r d)
local notation "φ"=> tall F (d+1)
local notation "A₁"=> A.m ∘ q
local notation "E₁"=> E.m ∘ q
local notation "B₁"=> O.m ∘ v
local notation "p"=> Sum.elim q v
local notation "♥"=>F.value L
private def mobility (d r:ℕ):= 2*(d + 3*r)
def issuance (d r:ℕ):= geese d + 4*(d+3*r)
lemma issuance_eq (d r:ℕ): issuance d r=geese d+mobility d r+mobility d r:= by unfold issuance mobility; omega
include HO
lemma inventoryF : Inventory e F q v T C r d := ⟨HO.law.order (tollLe F d), HO.le,
   fun i=> (Tier.gain_moment F _ (fun k=> T.sign (q i) (p k)) _ (tollLe F d)).trans (HO.ready i), HO.nn, HO.mind, HO.cog⟩ -- projection ambiguity
lemma voice (P:Channel I)(hp:Guard P r d): F.gain B₁ (e.floats P) r ≤ C^expansive d r * (tall F (d+1)).gain (O.m ∘ q) P r := by
 have H := inventoryF HO; exact (rough O H.law H.le H.ready H.nn H.mind H.cog P hp).trans (mul_le_mul_of_nonneg_left (Tier.gain_moment F _ (fun i=> O.sign (q i)) P (tollLe F d)) (pow_nonneg (le_trans (by norm_num) H.nn) _))

private lemma paid_row (O:Lens T)(P:Channel I)(hp:Guard P r d): (φ).gain (O.m ∘ p) (replot e.spur P) r ≤ C^mobility d r * (φ).gain (O.m ∘ q) P r:= by
 have hz:= HO.nn; have hx : 0≤ C:=by linarith
 apply le_trans (thoughts (fun i=> O.sign (p i)) (fun i=> O.sign (q i)) (Roads.rich T q p _ _ _ _ HO.ready O) (Roads.rich T q p _ _ _ _ (Roads.cashfree T _ _ _ _ _ _ HO.ready) O) hx P hp.slim (by linarith)); unfold mobility; rw [pow_mul C]; apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by nlinarith) _) (Tier.collect (φ) (O.m ∘ q) (fun i=> O.sign (q i)) _)
-- ledger.Total.Gain. Schur h required before linking for all locations.
lemma park (P Q:Channel I)(hs:Guard P r s)(ht: Guard Q r t) (hi:s+t+3*r≤d) (ho: O.m≤A.m)(hx:O.m≤E.m)(hh:0≤L)(h:A.Spaced E L) : F.value L*F.gain (O.m ∘ v) (e.error P Q) r ≤ C^issuance d r * (tall F (d+1)).gain A₁ P r * (tall F (d+1)).gain E₁ Q r := by
 have h' := HO.cog; have h0:=(show 0≤ C from le_trans (by norm_num) HO.nn)
 let X := replot e.spur; let f := X P; let g := X Q
 have he : PaidPair e.joint e.vertices T p F C L O A E r d:= Rupture.paid O A E HO.law HO.le.rank e.law ho hx HO.nn (by linarith) (by linarith) HO.mind hh h
 have hp:=Guard.prep hs e.spur HO.le.spur; have hq:=Guard.prep ht e.spur HO.le.spur
 have hx':O.m ∘ v=O.m ∘ (p ∘ Sum.inr):=rfl
 rw [hx',Episode.effect]; apply (grain O A E he hh f g HO.nn HO.mind hi hp hq).trans; rw [issuance_eq,pow_add,pow_add]
 apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (paid_row HO A P (Guard.mono hs (by omega))) (pow_nonneg h0 _)) (paid_row HO E Q (Guard.mono ht (by omega))) (Tier.collect (φ) _ (fun x=>E.sign (p x)) _) (mul_nonneg (pow_nonneg h0 _) (mul_nonneg (pow_nonneg h0 _) (Tier.collect _ A₁ (fun x=>A.sign (q x)) _)))) -- anti which A? inspect
 exact le_of_eq (by ring)
end YM.FormalOPE.RG10.Rupture
