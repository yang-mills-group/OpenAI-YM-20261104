import YM.LocalLTE.Port.Berry
import YM.MergeProof.Zing
/-! # transporting inherited K burst to compact hats.

There is no assumption that at passing tests a nonzero certificate is attained. Numerators evaluated with exact internal predicates at EVERY index. We don't allow reducing support from that projection!
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a₀ c₁ a β:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
variable (h:B.Active)(hw:B.Radial r a₀ a v c₁)
open Push.AbsoluteSums Push.AbsoluteSums.Animals
-- refresh envelope at radius.Outward keeps.Their permits.Widget Pack
abbrev Node (B:Bands R Q):= {y:ℕ×ℕ // B.entries y.1 y.2 ≠ 0}
local notation "NX"=> Node B
abbrev skit (B:Bands R Q):= {y:R.Mode × Box f// y.1.val.Nonempty ∧ y.1.val.image B.origins⊆ y.2.1 ∧ y.2.2.Nonempty ∧ y.2.2⊆ y.2.1}
local notation "LX"=> skit B
local notation "q"=>barcode Q.activities
def billows (p:Node B) : skit B:= ⟨(B.marks p.val.1 p.val.2,barcode Q.activities p.val.1),h.occurs _ _ ,by
    intro i hi; obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact h.retained _ _ p.property _ hj,(Q.activities.forced p.val.1).inventory_ne,(Q.activities.forced p.val.1).inventory_sup⟩
local notation "X"=> billows B h
abbrev Token (p:skit B):Foot f:= ⟨p.val.2.1,p.val.2.2,p.property.2.2.1,p.property.2.2.2⟩
variable (hs: HasSlots Q.p Q.activities)
abbrev youngK (p:skit B):= sleepK G f (Port.Token B p,0)
include hs
omit [Fintype V] in
lemma locator (p:skit B): barcode Q.activities (youngK B p)= p.val.2 ∧ ∀ V,p.val.2.1 ∩ RG.flags ν V=p.val.2.2 → (Q.activities.forced (youngK B p)).eligible ν V:=by
    let i:= youngK B p
    have he: readFoot (Q.activities.forced i)= Token B p:=by rw [hs.forced]; exact tile_exact ..
    have hT: barcode _ _= _:= (show barcode Q.activities i=p.val.2 from Prod.ext (congr_arg Foot.support he) (congr_arg Foot.inventory he))
    refine ⟨hT,fun V h=>?_⟩ -- fix blank hole syntax
    change ForcedAddress.eligible (Q.activities.forced i) ν V
    exact ⟨(congr_arg (·∩ flags ν V) (congr_arg Foot.support he)).trans (h.trans (congr_arg Foot.inventory he).symm), (by rw [hs.forced]; exact (tile_test _ _ _ V).2 h)⟩
omit hs
def sprites (p:skit B) (z:Config G f):= cram (billows B h) (fun i=> B.entries i.val.1 i.val.2 z) p
local notation "s'"=> sprites B h
include h hw
-- local K policy.Minted.Truth.F. Note marker budget sums finite J.Count absorption.Dimension.Cipher.
abbrev chargeP (p:skit B):= p.val.1
local notation "A₀"=> Token B
--
-- construct input `Cover`. every Γ.Space count.L.X
lemma seatsK : ∃ b:Node B→ℝ,(∀ i,0 ≤ b i)∧ (∀ i Z, ‖B.entries i.val.1 i.val.2 Z‖ ≤ b i)∧
    SumBudget (fun i=> Marker.Poly.toll r ((X i).val.1)*Q.p.mass ((X i).val.2.1) (b i)) ((Fintype.card V)*(v*c₁)):=by
    obtain ⟨b,hK,hT⟩:= hw.hits; let f (z:ℕ×ℕ):= Poly.toll r (B.marks z.1 z.2)* Q.p.mass (Q.activities.forced z.1|>.support) (b z)
    have hh(i):0≤ f i:= mul_nonneg ((Poly.worth hw.pure _).le) (mul_nonneg (Real.exp_nonneg _) (hK i.1 i.2|>.1)); have hy:= Overlay.per_system hh (fun i=> h.occurs i.1 i.2) hT
    exact ⟨fun i=> b i.val,fun i=> hK _ _|>.1,fun i=> (hK _ _).2,budget_pull Subtype.val Subtype.val_injective hy⟩
-- Reads.Beaks.
omit hw
variable (b:Node B→ℝ)(hb:Summable b)(he:∀ i z,‖B.entries i.val.1 i.val.2 z‖≤b i)
include hs
include b hb he
omit [Fintype V] in
lemma sealK(p:LX)(i:Bool):∃ M: Menu.Hat R Q, originQ R B.origins M ∧ M.M.turn= Lotus.Wing.gasKey (youngK B p)∧M.M.ingredient = scaleQ i ∘ sprites B h p ∧ M.s=p.val.1 ∧ M.M.weight=cram (billows B h) b p ∧ M.charge= ink i:=by
    let L:=youngK B p; let U:=Q.activities.forced; have hz:= locator B hs p
    let r':= (U L).support; have hx': r'=p.val.2.1:= congr_arg Prod.fst hz.1
    let Z(p:Node B):= p.val.1; let k:={i:Node B// X i=p}
    let S': k→ Config G f→ℂ:= fun j=>B.entries j.val.val.1 j.val.val.2
    have hp(j:k):q (Z j.val)=p.val.2:=congr_arg (fun i:LX=> i.val.2) j.property
    have h'(j:k): (U (Z j.val)).support=r':= (congr_arg Prod.fst (hp j)).trans hx'.symm
    let t:= scaleQ i; let f':= t ∘ sprites B h p; have hr(j:k): UsesFinal ν r' (S' j):= (h' j) ▸ (show UsesFinal ν (U (Z j.val)|>.support) (S' j) from h.inspects j.val.val.1 j.val.val.2)
    have hi: (p.val.1).val.Nonempty:= p.property.1
    refine ⟨⟨⟨.gasKey L, f',?_,?_,trivial,cram X b p,?_,?_,?_⟩,p.val.1,hi, ink i⟩,?_,rfl,rfl,rfl,rfl,rfl⟩ -- Blank
    · intro Z V huv ht; refine congr_arg t (tsum_congr fun i=>hr i _ _ huv ht)
    · intro V hV; refine hz.2 V ?_
      by_contra hT; apply hV; suffices hx:(sprites B h p V)=0 from (congr_arg t hx).trans (t.map_zero) -- edit
      unfold sprites cram; refine (tsum_congr (fun j:k=>?_) : (∑' j:k,S' j V)=∑' _:k,(0:ℂ)).trans tsum_zero
      by_contra hp'; obtain hh':=(h.keeps _ _ V (show S' j V≠0 from hp')).1; have hz:=(hp j); let k':= (U (Z j.val)); have h: k'.support∩ flags ν V=k'.inventory:=hh'
      exact hT ((congr_arg (·∩ flags ν V) (congr_arg Prod.fst hz).symm).trans (h.trans (congr_arg Prod.snd hz)))
    · intro V
      let F(j:k):= S' j V; have ht(j):‖F j‖ ≤ b j.val:=he _ _; have hh:= hb.comp_injective (show Injective (Subtype.val : k→_) from Subtype.val_injective); have ha : Summable fun i=> ‖F i‖:= hh.of_nonneg_of_le (fun i=> norm_nonneg _) ht
      exact (stepColor i _).trans ((norm_tsum_le_tsum_norm ha).trans (ha.tsum_le_tsum ht hh))
    · intro t' Z; exact congr_arg t (tsum_congr fun j:k=> h.invi ..) -- Gauge.simp. edit
    · apply t.continuous.measurable.comp (Measurable.tsum (fun j:k=> h.meas j.val.val.1 j.val.val.2))
    change (p.val.1).val.image B.origins⊆ r'; rw [hx']; exact p.property.2.1
end YM.LocalLTE.Port
