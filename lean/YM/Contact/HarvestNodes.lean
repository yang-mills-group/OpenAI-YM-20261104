import YM.Contact.RangeFees
import YM.Contact.Branch
import YM.MergeProof.West.Ozone
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d w:ℕ)(h:ℤ)
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
open Accent Source Extra.Histories
variable (V: C.label d) (T:C.label w) (hp:(D:ℤ)+h=d+w) {u ψ:ℕ→ℝ}{W:Worth} (hG:G.Simple)(hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
variable (hV:Velour C (renal C.path.levels) r D')(p k:ℕ)(L:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 p k)
structure RangeNodes : Prop where
   fees : ∀ (d w D:ℕ)(h:ℤ),(D:ℤ)+h=d+w → ∃ (t:ℝ)(j:ℕ→ℕ), 1<t∧ Tendsto j atTop atTop ∧ Tendsto (fun i:ℕ=>Q (j i)/Q i) atTop (𝓝 t) ∧ ∀ p k:ℕ,Stock.Tabs.opens C.path.levels 1 p k→C.ref D ≤ k →∀ (v:C.label d)(T:C.label w)(F:Extraction.Order), ∀ᶠ i in atTop, RichNode C p (j i) i D d w h v T F (2*(stakes C p k / pitts C i))
include hW hG L hV
variable (hTally:Tally C.path.levels)
include hTally
lemma tolls (ht:Created C)(h:C.Makes): RangeNodes C:=by
   obtain ⟨χ,h'⟩:= hV.mother
   constructor; intro d w D l hp
   let a:ℝ:= (d:ℝ)+(w:ℝ)+8; let t:=1+1/(64*a); have ha:0<a:=by unfold a; positivity
   have he:1<t:=lt_add_of_pos_right _ (by positivity); have ht':a*(1-t) > -(1/32):=by rw [show a*(1-t)= -(1/64) by unfold t; field_simp; ring]; norm_num
   obtain ⟨j,hj,hh,hT⟩:= trapeze C.S t he C.path.levels.fits.mesh; refine ⟨t,j,he,hj,hT,fun p k hx hK v y F=>?_⟩
   let b:=max 1 ((C.labels.level w).coeffSize y); let z:= max 1 ((C.labels.level d).coeffSize v)
   have hb:0<b:=zero_lt_one.trans_le (le_max_left ..); have hw:0<z:=zero_lt_one.trans_le (le_max_left ..)
   filter_upwards [priced C D d w l hG t hT hj hV hb hw hp hW hTally k hK ht', lampDown C hG hV p,eventually_ge_atTop k,hj.eventually_ge_atTop (C.ref d), hj.eventually_ge_atTop (C.ref w), hh,Push.GridApprox.plenty C.path.levels p (lensScope C D)] with i ⟨⟨he,hp⟩,hϑ⟩ ⟨hM,hL⟩ hN hK' hI hj' hU
   exact toggled C p k (j i) i D d w l v y hx.1 hN hj' F h ht hW b z _ _ _ _ (le_max_right ..) (le_max_right ..) hw hb (Real.exp_pos _) L hx hK hK' hI hM (renal _) (bling _) (h' D) (hK.trans hN) rfl rfl hU (by push_cast at hL; exact hL) hp he (le_refl _) hϑ
end YM.MergeProof.Ribbons
