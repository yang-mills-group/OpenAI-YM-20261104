import YM.OPE.Compatible.Maestro.Lanes
/-!
# Survives full projection at head, under only *input* calibration direction
for TRUE lifts
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank.Spindle Next.UVStress
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot Series
variable {V:Type}[PartialOrder V][OrderBot V][Fintype V](D:Origin V) {Q:Finset V}{m j k:V→ℕ}
    {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book} {U:Spec.Final C F S}{a:ℝ}{W J K n b d:ℕ}
-- bridge to survival single estimate times all rows
open Pixel
variable {y:V→ Cover}(v: brim D Q→ C.book.Token)(u:brim D Q→ℝ)
set_option quotPrecheck false
local notation "x"=> CutOrder.grove D C Q m j a u
variable (hG:G.Simple)(A:Allot C)(hC:C.Makes)(H:Series Q m) {l:ℕ→ℕ}
include hG hC H
lemma marvel (h : Positioned C D Q m k b J W l y)(ht:∀ i,m ⊥ ≤ i→ places V≤ A.r i)
   (hx:Stock.Tabs.opens C.path.levels 1 J K)(hK:C.ref d≤ K)(hw:K≤ n)(hp:n+1=m ⊥)(hv: CutOrder.Expenses C D Q m (fun i=>min (k i) (m i)) (fun i=>81*(l i+1)) b a)
   (hb: 1 ≤ b)(hr: Push.GridApprox.room C.path.levels J n (lensScope C d))(hu:∀ i,0<u i) (hζ:∀ i:brim D Q,C.ref (v i).1 ≤ j i.val ∧ j i.val+1=k i.val)
   (f:Filter (ℕ×ℕ))(hf:f.NeBot)(he:f ≤ F.fuse)(hP:∀ᶠ a in f,∀ i:brim D Q,2*u i * Next.Rank.Spindle.paid C (v i).1 (k i.val) a.1 a.2 (v i).2 ≤ fly C.path.levels (v i).1 (k i.val)):
    ∃ q,Survival (C:=C) F J n W (2*(stakes C J K / rebate C x d K n)) (2*owed C x d n) v (y ∘Subtype.val) d q:=by
   let s := 2*(stakes C J K/rebate C (x) d K n); let g:=CutOrder.grove D C Q m j a u; let e:=2*owed C g d n
   have hh:= marched D A hG hC H y v u h hx hK hw hp hv hb ht hr hu hζ
   let t(i:ℕ×ℕ)(q:C.label d):= Cards.PaidAt C.S i.1 i.2 J (C.beta i.1 i.2) s (Cards.register C W (y∘Subtype.val) (germ (frozen C v)) i.1 i.2-C.O i.1 i.2 q 0)∧ Next.UVStress.quota C d n i.1 i.2 q ≤ e
   let r(i:ℕ×ℕ) := ∀ u':brim D Q, 2*u u'* paid C (v u').1 (k u'.val) i.1 i.2 (v u').2 ≤ fly C.path.levels (v u').1 (k u'.val)
   have hΩ:∀ᶠ i in F.fuse,r i →∃ q,t i q:=by
      rw [Extraction.Order.fused, Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually hh] with p hp; exact F.mesh.cofinal.eventually hp
   have hi:∀ᶠ i in f,∃ q,t i q:= hP.mp (hΩ.filter_mono he)
   let z(i:ℕ×ℕ):= if h:∃ q,t i q then h.choose else 0; have hz:∀ᶠ i in f, t i (z i):= hi.mono fun i h=> by unfold z; rw [dif_pos h]; exact h.choose_spec -- precedence
   obtain ⟨E,hE,hL⟩:= quota_stop C hC (hK.trans hw)
   obtain ⟨T,hT,hY,q,hv⟩:=finite_extract (𝓛:=f) z (E*e) (by filter_upwards [hz,((Cards.largeMesh F).eventually_ge_atTop n).filter_mono he] with i h hh using (hL i.1 i.2 (z i) hh).trans (mul_le_mul_of_nonneg_left h.2 hE))
   exact ⟨_,hK.trans hw,T,z,hY,hT.trans he,hv,⟨(hz.mono fun i h=> h.1).filter_mono hT⟩,(hz.mono fun i h=> h.2).filter_mono hT⟩
end YM.OPE.Arboreal
