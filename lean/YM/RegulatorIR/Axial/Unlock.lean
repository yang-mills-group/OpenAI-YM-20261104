import YM.RegulatorIR.Axial.Kings

/-!
# Full W1 specification for moment Ward blocks (consume fixed array)
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck Finset
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G} (H:Reel S)(T:S.Accounts)
variable (V:H.Follows T)(hh:Common H)
variable {p e k:ℕ}{L:Meter W} (A:S.Supplies T L p k)(B:Aug.Amenities S L p k)
variable (v:Page M)
variable (hp:14≤k)

structure W1 (U:Orders (Foot G))(p:ℕ): Prop where
 grade (A:BEdge G) (σ:Cover→ G.Color) (h:(Function.support A).Finite)(h':(Function.support σ).Finite)(e:ℕ) : e ≤ p → rhymeR (vow (shadowU A σ)) U 2 e=rhymeR (vow (fun _=>hue A)) U 2 e
 signed (A:BEdge G)(h:(Function.support A).Finite)(u:Signed)(e:ℕ) : e≤p → rhymeR (vow (fun _=>hue (beast u A))) U 2 e= rhymeR (vow (fun _=>hue A)) U 2 e
 adjoints (A:BEdge G)(h:(Function.support A).Finite)(u:G.El)(e:ℕ) : e≤p → rhymeR (vow (fun _=>hue (vbadge u A))) U 2 e=rhymeR (vow (fun _=>hue A)) U 2 e

include A V hh B hp
lemma enabled (ht: Layer.Sym (S.maps v) (S.maps v) (H.stem v))(hr:Billed (H.stem v)): W1 (dyeX (H.stem v) (T.bulk v)) p:=by
 cases v with| mk w i h=>
 let v:Page M:=⟨w,i,h⟩; let c:= H.deep v; let f:= H.even v
 constructor
 · intro a σ hs hq e he
   let P:= hq.toFinset; let F:= P×ˢ(univ:Finset Axis); let X:= hs.toFinset; let Y:= X∪F;let Q:=Y∪F.image (fun i=> (i.1-step i.2,i.2))
   have H' : Function.support a ⊆ (↑Q:Set _):=fun _ hx=> mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (hs.mem_toFinset.mpr hx))))
   have hL : ∀ x,x∈Function.support σ → ∀ v:Axis,(x,v)∈Q:= fun x hx v=> mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_product.mpr ⟨hq.mem_toFinset.mpr hx,mem_univ v⟩))))
   have hR:∀ x, x∈Function.support σ →∀ v:Axis,(x-step v,v)∈Q:= fun x hx v=>mem_union.mpr (Or.inr (mem_image_of_mem _ (show (x,v)∈F from mem_product.mpr ⟨hq.mem_toFinset.mpr hx,mem_univ v⟩)))
   apply values H T V w hh A B i h hp ht hr (scriptK a σ c f Q H' hL hR) (scriptT a c Q H') he
   exact Eventually.of_forall fun z=> Or.inl (current_event _ (dropV_tag z c σ))
 · intro a h u e he;let F:=h.toFinset; have ha : Function.support a ⊆(↑F:Set _):=fun _=> h.mem_toFinset.mpr
   rw [← inv_inv u]
   apply values H T V w hh A B i (show _ from by assumption) hp ht hr (bookT u⁻¹ a F c f ha) (scriptT a c F ha) he
   exact Eventually.of_forall fun z=> Or.inr ⟨_,Eventually.of_forall fun t=>beat_rose (u⁻¹)⁻¹ (track z c a) t⟩
 intro a h u e he;let F:= h.toFinset; have ha:Function.support a⊆(↑F:Set _):=fun _=> h.mem_toFinset.mpr
 apply values H T V w hh A B i (show _ from by assumption) hp ht hr (bookA a u F c ha) (scriptT a c F ha) he
 exact Eventually.of_forall fun z=> Or.inl (Eventually.of_forall fun t=> ⟨_,(fun _=>rfl),sentB u (track z c a) t⟩)
end YM.RegulatorIR.Axial
