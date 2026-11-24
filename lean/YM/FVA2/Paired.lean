import YM.FVA2.FundingOffer
import YM.Contacts.Ion.Bench
/-!
# Identify the seam geometry exactly when attaching Cover Descent & Inversion Fabric

'S.Physical.History' remains the inversion torus, not replacing b flag.
But the qlocal companion option requires also spelling the algorithm on non-inverted periods
and keeping all orientation/accounting identities explicit. Pair the history of `T.Forestry`
with its descended inversion trees. NOT claiming CP12 Manor estimates for loop/winding here.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}{c f n:Side}

-- Symmetric tree geometry.Supplier - also chosen in Contacts.*. Identify projector
variable (S:StepData c f)
def canopy : Inside S.ratio:= Inside.project S.patch.odd_side ( Forestry S )

lemma equivalent_site {n:Side}{x y: Site n}(h:track x=track y): x=y∨x= -y:= by
     have hx: vertex x=vertex y:= congr_arg Subtype.val h; rcases vertex_spec x with ht|ht<;> rcases vertex_spec y with hy|hy<;> rw [ht,hy] at hx <;> first | exact Or.inl hx| exact Or.inr hx | exact Or.inl (neg_inj.mp hx)|exact Or.inr (by rw [←hx,neg_neg])

local notation "P"=> canopy S
local notation "T"=> Forestry S
lemma canopy_leaf (x:Site f) : ¬planted S.ratio (track x) ↔ Tree.leaf S.ratio x:= by
    refine ⟨ Inside.starts S.patch.odd_side _,fun m hx=>?_ ⟩
    unfold planted at hx; rw [ ancestral_track S.patch.odd_side, place_track ] at hx; rcases equivalent_site hx.symm with he|he; · exact m he
    let y : Site f:= S.ratio.embed (S.ratio.parent x); have ht : -x=y:= by unfold y;nth_rw 1 [he]; abel
    have hF : ¬ Tree.leaf S.ratio (-x):= not_not_intro (show -x=S.ratio.embed (S.ratio.parent (-x)) from ht ▸ (by unfold y; rw [S.ratio.embed_parent])) -- uses m ht rew? check
    exact hF (( pupil S x ).mpr m)
lemma branch_copied (i:Edge (Site f)): eR i∈ (T).trunks ↔ i∈ (T).trunks:= by rcases eR_spec i with h|h; rw [h]; rw [h,trunk]
lemma wire_copy (x:Site f) (hx: ¬planted S.ratio (track x)): (P).wire (track x) hx= PertExtension.Orb.index ((T).up x |>.used x) := by
    let v:= Inside.closer ( T ) (track x); change PertExtension.Orb.index (((T).up v).used v)= _; rcases equivalent_site ( Inside.closer_id ( T ) ( track x ) ) with h|h; · rw [ show v=x from h ];
    rw [show v= -x from h, Align.contour S x ((canopy_leaf S x).mp hx), used_flip ]; exact Subtype.ext (eR_reflect _)
lemma branch_ident (i:OEdge f): ( P ).Innate i ↔ i.val∈ (T).trunks:= by
    constructor
    · rintro ⟨v,h,rfl⟩; let x:=Inside.closer ( T ) v; change eR (((T).up x).used x)∈ _; apply (branch_copied S _).mpr; exact (Forest.trunk_mem_iff (T) _).mpr ⟨ x,Inside.close_leaf S.patch.odd_side ( T ) v h,rfl ⟩
    intro h; obtain ⟨x,hx,H⟩:= (Forest.trunk_mem_iff (T) i.val).mp h; have he : ¬planted S.ratio (track x):=(canopy_leaf S x).mpr hx; exact ⟨track x,he,by rw [ wire_copy S x he, H ]; exact Subtype.ext i.property⟩
end YM.FVA2.Both
