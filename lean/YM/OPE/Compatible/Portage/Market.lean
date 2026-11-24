import YM.OPE.Compatible.Portage.Zoned
/-!
# Norm prices on this true grid. Embedded words. Cutoff → continuum filters still to be used at fixed geometry. The Milestone sensitivities use cutoff true trajectory importance not continuum norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon Next.UVStress
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {Q:Finset X} {G:Gauge}{C:Family G}{m k z:X→ℕ}{J K j d b W:ℕ} {l:ℕ→ℕ}
open YM.OPE.Allot Series
variable (X0:Allot C)(hG:G.Simple)(hC:C.Makes)(S:Series Q m)
variable (c:X→ Cover) (v:brim D Q→ C.book.Token) (u:brim D Q→ ℝ){a:ℝ}
variable (h:Positioned C D Q m k b J W l c)
    (hx:Stock.Tabs.opens C.path.levels 1 J K)(hK:C.ref d ≤ K)(hw:K ≤ j)(hp:j+1=m ⊥)(he:CutOrder.Expenses C D Q m (fun i=>min (k i) (m i)) (fun i=>81*(l i+1)) b a)
    (hb: 1 ≤ b) (hA:∀ i,m ⊥ ≤ i→ places X ≤ X0.r i)(hr:GridApprox.room C.path.levels J j (lensScope C d)) (hu:∀ i,0<u i) (hζ:∀ i:brim D Q,C.ref (v i).1 ≤ z i.val ∧ z i.val+1=k i.val)
set_option quotPrecheck false
local notation "M"=> CutOrder.grove D C Q m z a u
local notation "I"=>brim D Q
include h hC hG hx hK hw hp hA he hb hr hu hζ S
-- eventual reproduction needs F.filter direct. threshold local costs leaf via manual atTop below.
lemma marched : ∀ᶠ p:ℕ in atTop,∀ᶠ N:ℕ in atTop,
     (∀ i: I, 2*u i * Next.Rank.Spindle.paid C (v i).1 (k i.val) N p (v i).2 ≤ fly C.path.levels (v i).1 (k i.val)) →
     ∃ y:C.label d, Cards.PaidAt C.S N p J (C.beta N p) (2*(stakes C J K/rebate C M d K j)) (Cards.register C W (c∘Subtype.val) (germ (frozen C v)) N p-C.O N p y 0) ∧ Next.UVStress.quota C d j N p y ≤ 2*(owed C M d j):=by
   filter_upwards [eventual_positioned D S h] with p hv
   filter_upwards [hv,(eventually_all.mpr fun i: I=> near_center C J (v i|>.1) hC),near_center C J d hC,eventually_gt_atTop j,eventually_ge_atTop W] with N ⟨hg,ht,hQ,hx',hY⟩ hy hz hN hl hh
   let V':= Site (C.side J p); let P:= CutOrder.listP C p J; let E:= Mix.camp C p J; let x(a:X):=Cells.location C.S W N p (c a); let Y (a:X):=axis C p N J (x a); let g(i: I):=C.O N p (v i).2 (Cells.location C.S W N p (c i)); let F:= Cards.register C W (c∘Subtype.val) (germ (frozen C v)) N p
   have hF:F=fun U=>∏ i,g i U:=by funext i; unfold F; rw [germ_here]; rfl
   have hi(i:I) : i.val∈allUp D Q:=Finset.mem_union_right _ i.2; have hJ:J ≤ N:=hx.1.trans (hw.trans hN.le)
   let T:=center C.S p hJ 0; have hu(i:I): Interior (T.chamber 0) (g i):=hy i hJ p _ (by rw [hY _ (hi i)]; exact h.fit i.val (hi i)) (v i).2 -- convert arg inference
   have he0(b:C.label d):Interior (T.chamber 0) (C.O N p b 0):=hz hJ p _ (by rw [latzero]; simp [(C.S.a_pos J).le]) _
   have hσ i : Y i N 0=x i:=at_zero_axis C p N J _ hJ
   have hW : ∀ i:I, C.ref (v i).1 ≤ z i.val ∧ z i.val < N ∧ finishAt D m i.val ≤ z i.val+1 ∧ Migrating C.path (z i.val+1) p N (Y i.val)∧ 2*u i*Next.Rank.Spindle.paid C (v i).1 (z i.val+1) N p (v i).2 ≤ fly C.path.levels (v i).1 (z i.val+1):=by
      intro i; refine ⟨(hζ i).1, (show z i.val+1 ≤ N from (hζ i).2.le.trans (ht _ (hi i))), ?_⟩; rw [(hζ i).2]; obtain ⟨ht,t,hT⟩:= hQ _ (hi i); refine ⟨h.ap _ (hi i),?_,hh i⟩
      rw [show Y i.val=axis C p N J ((C.S.toDepth ht p).embed t) from congr_arg (axis C p N J) hT]; exact reel C p N J (hx.1.trans (hw.trans (j.le_succ.trans (hp.le.trans ((lower_earliest D Q m S i.val (hi i)).trans (h.ap i.val (hi i))))))) ht t
   obtain ⟨z,hr,hU,hG⟩:= CutOrder.fullyJoined D (fun i=>(v i).1) (fun i=>(v i).2) u (clocked D S x hg) he X0 hC hG hx hw hp hN hK hA hr ((congr_arg (axis C p N J) (show x ⊥=0 from hx')).trans (axis_zero ..)) hb (by assumption) hW F (funext fun V=> (congr_fun hF V).trans (Finset.prod_congr rfl fun i _=> by rw [show axis C p N J (x i.val) N 0 = _ from hσ _])) (hF ▸ Interior.combines g _ (fun i _=>hu i)) he0
   exact ⟨_,⟨hJ,hU,hG⟩,hr⟩
end YM.OPE.Arboreal.Pixel
