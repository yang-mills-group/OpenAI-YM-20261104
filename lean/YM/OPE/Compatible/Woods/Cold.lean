import YM.OPE.Compatible.Woods.Heat
import YM.Next.FREE_KERNELS.Hall
/-!
# Fixed-factor free slice inverse; width still uniformly priced, other periods read same chart. Difference compares on kinetic, not metric. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*} {c f L:Side}{t: ℕ}{P:Patch}{C:KernelChoices}{η v A s: ℝ}
open Frequency
lemma scope_bill (P: Patch)(G:Gauge)(C:KernelChoices)(h:4≤t) : ∃ s B:ℝ, 0<s ∧ 0≤B ∧ ∀ D: Train t,(forge P C G D).strip s B:=by
    obtain ⟨s,M,he,hM,hg⟩:= (heart_heats C.penalty C.penalty_pos h (fun i:Train t=>i)).1.stock.uniform
    simp only [mul_one] at hg
    exact ⟨s, _,he,outputPrice_nn P C.penalty s M hM.le, fun D=> hedge_width (hg D) he hM.le⟩
structure Medal (P: Patch)(G: Gauge)(C:KernelChoices)(t:ℕ) where
   V : Train t→ Row (Slip G P.L) (Slip G P.L)
   gap : ℝ
   width : ℝ
   crown : ℝ
   root : 0<gap
   toll : 0<width
   deep (D : Train t)(c:Side): Gap ((forge P C G D).acts c) gap
   reads (D:Train t)(c:Side): (V D).acts c = ((forge P C G D).acts c)⁻¹
   price (D: Train t): (V D).strip width crown
lemma medal_buy (hp:Odd P.L.val)(hb:P.Branches C G)(h:4≤t) : Nonempty (Medal P G C t):=by
   let S:= Slip G P.L
   obtain ⟨s,M,hs,hM,hS⟩:= scope_bill P G C h
   have hy:= (heart_heats C.penalty C.penalty_pos h (fun i:Train t=>i)).1
   obtain ⟨v,B,hv,_,h⟩:=hy.funds
   let r:=treeFare G P C v; have hr:0<r:=treeFare_pos _ _ _ hv
   have hj(D:Train t)(c:Side): Gap ((forge P C G D).acts c) r:= hedge_gap (hy.stock.whole D) hp hb (fun n => ⟨fun k=> ((obey_band _ (hy.stock.whole D) (h D) n).2 k).1⟩) hv c
   let q:= FreeResolvent.margin S s M r; have he:0<q:= margin_pos _ hs hM hr
   choose Q hQ H using fun D:Train t=> strip_resolvent (forge P C G D) (u:=0) le_rfl hr hs hM (hS D) (hj D) (show q/2< FreeResolvent.margin (Slip G P.L) s M r from half_lt_self he)
   exact ⟨⟨Q,r,q/2,_,hr,half_pos he,hj,fun D n=> by simpa [resolve] using H D n,hQ⟩⟩
namespace Medal
variable (B: Medal P G C t)
lemma whole (D:Train t): Whole (B.V D) :=⟨_,_, B.toll, B.price D⟩
lemma static (D:Train t)(c:Side):
   (forge P C G D).acts c * (B.V D).acts c=1 ∧ (B.V D).acts c * (forge P C G D).acts c=1:= by
      have ht:= (B.deep D c).unit_det B.root; rw [B.reads]
      exact ⟨Matrix.mul_nonsing_inv _ ht, Matrix.nonsing_inv_mul _ ht⟩
def visits := ((Fintype.card (Slip G P.L) :ℝ)*B.crown)^2 * (Fintype.card (TypeFace 1):ℝ)
lemma approach (D E: Train t)(h:4 ≤ t)(hs:0<s)(hW:s ≤ B.width)(hp:(Op C E-Op C D).strip s A): (B.V D-B.V E).strip s (B.visits*A):=by
   let W := B.V D; let U:= B.V E; let R:= forge P C G E - forge P C G D
   have hsR: R.strip s _:= hedge_trains E D h hs hp
   let V := composeRows (composeRows W R) U
   have hV: V.strip s (B.visits*A):= by
       apply strip_mono (strip_compose (P:=composeRows W R) hs.le (strip_compose hs.le (strip_mono (B.price _) hW le_rfl) hsR) (strip_mono (B.price _) hW le_rfl)) le_rfl; unfold visits; exact le_of_eq (by ring)
   have hz: B.V D-B.V E = V:= by
       apply bank_injective ((B.whole D).minus (B.whole E)).safe (Whole.safe (show Whole V from ⟨_,_,hs,hV⟩))
       intro n
       obtain ⟨s,m,ht,hM,hZ⟩:=scope_bill P G C h
       have hw (d:Train t): Whole (forge P C G d):=⟨_,_,ht,hZ d⟩
       have hr:Whole R := (hw E).minus (hw D)
       change (minusRows W U).acts n = _; rw [(B.whole D).less (B.whole E),(show V=composeRows (composeRows W R) U from rfl), ((B.whole D).prod hr).acts (B.whole E),(B.whole D).acts hr]; rw [show R.acts n=_ from (hw E).less (hw D) n,Matrix.mul_sub,Matrix.sub_mul]; rw [Matrix.mul_assoc, (show _ * U.acts n= _ from (B.static E n).1), (show W.acts n * _ =_ from (B.static D n).2), Matrix.mul_one,Matrix.one_mul]
   rw [hz]; exact hV
end Medal
end YM.OPE.Woody
