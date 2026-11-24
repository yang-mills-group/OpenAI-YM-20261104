import YM.OPE.Screens.Peer
import YM.OPE.Screens.Break
import YM.OPE.Trees.Audience
import YM.OPE.Screens.Compass
/-!
# Read quote from actual scenes with the one before-determined detector convention

Used either at root, OR translated within cluster for an ancestor-reader.
Scopes of allowance are prices at one pose, chosen before a finite forecast.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec
open Rhythm Payments
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
    {H t n b k l d e:ℕ}{Q: Rhythm I}{C: Family G}
set_option quotPrecheck false
variable {F:Extraction.Order}{S:Table C.book}(U: Final C F S)
variable {Y:Type}{f:Filter Y}{x:Y→ I→ Cover}{X:Y→ I→ E4}{y:Y→ E4}{T a a' o q c : Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{η M:ℝ}
    {P:Y→Loom Q} {B: Border f T Q.limit R r α} (D:Oscars B M P C)
    (w:Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)} (h:φ ≤ F.fuse) {k':Y→ℕ}
    (LL : Org.Grill C F)
local notation "μ!"=> C.S.a
local notation "L!"=> (fun i=> (P i).launch Q.limit)
local notation "K"=> C.path.levels.budget
local notation "T!"=> C.S.gridPoint
variable (v:I→ C.book.Token)
local notation "v'"=> (fun j=> (v j).1)
local notation "m!"=> (fun i=>(P i).below 0)
local notation "μ"=> (fun i t=> (P i).launch t)
local notation "κ"=> Wallet f T
local notation "ξ!"=> (fun i=> C.S.gridPoint (k' i) ∘ x i)
local notation "Z!"=> (fun i=> priceSet Q univ v (R i))
local notation "D0"=> U.sector.derivatives
open Probe
namespace Booking
-- choose horizons for set of requested words, arbitrary expected.Mᵢ translations pass along absolute
abbrev v0 : Unit→E4:= sole 0
abbrev Seats (C: Family G)(F:Extraction.Order) (b:ℕ)(f:Filter Y)(y:Y→ E4)(q:Exterior C.book) : Prop := ∃ (c:ℝ), 0<c∧ ∃ α, Viewer C F q.letter b c α ∧ ∀ᶠ i in f,ClearOf 0 (Arboreal.register q (y i)) c
include U in
lemma enough (p: Finset (Exterior C.book))(hz:Tendsto (fun i=> ‖y i‖) f (𝓝 0)): ∀ᶠ b in atTop,∀ q∈p, Seats C F b f y q:=by -- needs U
    refine (eventually_all_finset p).mpr fun i hi=>?_; obtain ⟨c,hc,h'⟩:= (Arboreal.shelf (φ:=f) i y).at (z':=fun _=>0) (show Tendsto _ f _ from by simpa using! hz); filter_upwards [arrivals U i.letter hc] with b hb using ⟨c,hc,hb.choose,hb.choose_spec,h'⟩
lemma zeroed (hz:Tendsto (fun i=> ‖y i‖) f (𝓝 0)) {y':E4} (hY:y'=(0:E4)): Tendsto (fun i=> ‖y i-y'‖) f (𝓝 0):= by simpa [hY] using hz
-- template no need permit.Capt reader Origin.Word.Cases
lemma atomic {p:Y→J→E4}(hX:∀ j,Tendsto (fun i=> ‖X i j‖) f (𝓝 0))(hp:∀ᶠ i in f,Injective (X i))(h:∀ᶠ i in f, ClearOf 0 (p i) η)(he:0<η): ∀ᶠ i in f,Injective (beside (X i) (p i)) ∧ Injective (beside v0 (p i)):=by
    have hc:= eventually_all.mpr (fun i:I=> (hX i).eventually (gt_mem_nhds he)); filter_upwards [hp,hc,h] with i hp hf h
    have hz:Injective (p i):=by intro j k he'; by_contra hc; have ht:=he.trans_le (h.spread j k hc); rw [he',sub_self,norm_zero] at ht; exact (lt_irrefl _ ht)
    refine ⟨beside_distinct.mpr ⟨hp,hz,fun j k h'=>?_⟩,beside_distinct.mpr ⟨injective_of_subsingleton _,hz, fun j k h'=>?_⟩⟩; · have he := h.openSpace k; rw [← h',zero_sub,norm_neg] at he; exact (hf j).not_ge he
    have ht:= h.openSpace k; change 0=p i k at h'; rw [← h', sub_self,norm_zero] at ht; exact he.not_ge ht

-- frame translated through full Exposure tube.Y.Space rotations.
variable {P':Prescription U.sector.derivatives}{z:Y→ C.label d}
local notation "f!"=> (fun i q=> Arboreal.register q (y i))
local notation "Χ"=> (fun i: Y=> C.S.gridPoint (k' i) ∘ x i)
local notation "Ζ!"=> (P'.sheet w).support
variable (hZ:∀ᶠ i in f,Screen (C.S.gridPoint (k' i) ∘ x i)) (hX:∀ j,Tendsto (fun i=> ‖C.S.gridPoint (k' i) (x i j)‖) f (𝓝 0)) (hV:∀ q∈ (P'.sheet w).support, Seats C F b f y q) (hy:Wallet f T (fun i=> c i*o i))
    (hu:∀ᶠ i in f, 0 < c i) (hk:∀ᶠ i in f,b≤ k' i) (hT:Tendsto T f atTop)
local notation "q!"=> (fun j=> P'.ope w (Χ j) v (y j))
local notation "o!"=> (fun i d (z:C.label d)=> P'.ope w v0 (negative z) (y i))
include U hZ hX hy hV hu hT hk LL h
lemma firstTicket {m:Y→ℕ} (he:∀ᶠ i in f, Dir C S (k' i) b (m i) d (a i) (o i) (x i) v φ (z i)): Wallet f T (fun i=> c i • (P'.ope w (Χ i) v (y i)-P'.ope w v0 (negative (z i)) (y i))):=by
    let p(q':Exterior C.book)(i):= (P'.sheet w) q' * (Prescription.reading S (Χ i) v (y i) q'-Prescription.reading S v0 (negative (z i)) (y i) q')
    have hx(q')(hp:q'∈ (P'.sheet w).support): Wallet f T (fun i=> c i • p q' i):=by
       obtain ⟨d,hd,A,hV,hA⟩:= hV q' hp; have hK:= atomic (X:=Χ) hX (hZ.mono (fun i hi=>hi.coin)) hA hd; apply (((Wallet.const hT ‖(P'.sheet w) q'‖).mul (hy.mul (Wallet.const hT A)))).of_est
       filter_upwards [hK,hZ,he,hA,hk,hu] with i hx hZ he hA hk hu; unfold p; rw [Arboreal.record_raw _ _ U.room.kernel _ hx.1,Arboreal.record_raw _ _ U.room.kernel _ hx.2,norm_smul,norm_mul,Real.norm_of_nonneg hu.le]; have hp := Probe.root_read U h hV LL hk (Y:=Arboreal.register q' (y i)) none he hZ hx.1 hx.2 hA; let C':= ‖(P'.sheet w) q'‖; let x':= Χ i; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hu.le).trans_eq (by ring)
    unfold Prescription.ope; simp_rw [← sum_sub_distrib,←mul_sub,Finset.smul_sum]; exact Wallet.sum hT hx

variable {z':Y→ C.label e}{d':Finset I}
local notation "v!"=> (chunk d' v)
lemma childTicket {a a' o':Y→ℝ}{m l:Y→ℕ}(he:∀ᶠ i in f, SignDir C S (k' i) b (m i) (l i) d e (a i) (o' i) (a' i) (o i) (x i) v d' φ (z i) (z' i)) : Wallet f T (fun i=> c i • (P'.ope w (chunk d' (Χ i)) (chunk d' v) (y i)-P'.ope w v0 (negative (z' i)) (y i))):=by
    let p(q': Exterior C.book)(i):= (P'.sheet w) q' * (Prescription.reading S (chunk d' (Χ i)) v! (y i) q'-Prescription.reading S v0 (negative (z' i)) (y i) q')
    have hx(q')(hp:q'∈ (P'.sheet w).support): Wallet f T (fun i=> c i • p q' i):=by
       obtain ⟨d,hd,A,hV,hA⟩:= hV q' hp; have hK:= atomic (X:=Χ) hX (hZ.mono (fun i hi=>hi.coin)) hA hd; apply (((Wallet.const hT ‖(P'.sheet w) q'‖).mul (hy.mul (Wallet.const hT A)))).of_est
       filter_upwards [hK,hZ,he,hA,hk,hu] with i hx hZ he hA hk hu; unfold p; rw [Arboreal.record_raw _ _ U.room.kernel _ (affiliate (s:=d') hx.1),Arboreal.record_raw _ _ U.room.kernel _ hx.2,norm_smul,norm_mul,Real.norm_of_nonneg hu.le]; have hp := Probe.signLeaf U h hV LL hk (Y:=Arboreal.register q' (y i)) none he hZ hx.1 hx.2 hA; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hu.le).trans_eq (by ring)
    unfold Prescription.ope; simp_rw [← sum_sub_distrib,← mul_sub,Finset.smul_sum]; exact Wallet.sum hT hx
lemma mainTicket {a a' o':Y→ℝ}{m l:Y→ℕ} (hs:∀ᶠ i in f, Screen (substituted d' (C.S.gridPoint (k' i) ∘ x i))) (he:∀ᶠ i in f, SignDir C S (k' i) b (m i) (l i) d e (a i) (o i) (a' i) (o' i) (x i) v d' φ (z i) (z' i)) : Wallet f T (fun i=> c i • (P'.ope w (Χ i) v (y i) - P'.ope w (substituted d' (Χ i)) (substituted_row d' v (z' i)) (y i)-P'.ope w v0 (negative (z i)) (y i))):=by
    let p(q':Exterior C.book)(i):= (P'.sheet w) q' * ((Prescription.reading S (Χ i) v (y i) q'-Prescription.reading S (substituted d' (Χ i)) (substituted_row d' v (z' i)) (y i) q')-Prescription.reading S v0 (negative (z i)) (y i) q')
    have hx(q')(hp:q'∈(P'.sheet w).support): Wallet f T (fun i=> c i • p q' i):=by
       obtain ⟨d,hd,A,hV,hA⟩:=hV q' hp; have hK:= atomic (X:=Χ) hX (hZ.mono (fun i hi=>hi.coin)) hA hd; apply (((Wallet.const hT ‖(P'.sheet w) q'‖).mul (hy.mul (Wallet.const hT A)))).of_est
       filter_upwards [hK,hZ,hs,he,hA,hk,hu] with i hx hZ hs he hA hk hu; let Pq i:= Χ i; let y':= f! i q'; have ht: Injective (beside (substituted d' (Pq i)) y'):= by
           obtain ⟨_,hz,hA⟩:=beside_distinct.mp hx.1; refine beside_distinct.mpr ⟨hs.coin,hz,?_⟩; rintro (j|j) k; exact (beside_distinct.mp hx.2).2.2 () _; exact hA j.val k
       unfold p -- actually let binder shadow.fix
       rw [Arboreal.record_raw _ _ U.room.kernel _ hx.1,Arboreal.record_raw _ _ U.room.kernel _ ht, Arboreal.record_raw _ _ U.room.kernel _ hx.2,norm_smul,norm_mul,Real.norm_of_nonneg hu.le]; have hp:= Probe.signMain U h hV LL hk (Y:=y') none he hZ hs hx.1 hx.2 ht hA; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) hu.le).trans_eq (by ring)
    unfold Prescription.ope; simp_rw [← sum_sub_distrib,←mul_sub,Finset.smul_sum]; exact Wallet.sum hT hx
end Booking
end YM.OPE.Log.Trunk.Shuttle
