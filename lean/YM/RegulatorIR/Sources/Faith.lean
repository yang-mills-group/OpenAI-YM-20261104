import YM.RegulatorIR.Sources.Pyramid

/-!
# Faith: the bulk source report pays preimages by exact mass and stencil

Scalar and field parts, center x arbitrary, relative timing includes m+e
per-axis derivatives. One stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
variable {F:Labels.Frame G d}{H:Hol G} (Z: Fabric R F H)(Φ: W→ PhaseTests d)

def frown (w:plane W):= Z.readB w.1 w.2 (Φ w.1)
def fresco : (portraitR T).Report d:= declaring (portraitR T) (fun w=> Z.drawnU w.1 w.2 (Φ w.1)) (fun w=> (Z.depicts w.1 w.2 (Φ w.1)).2)
lemma spoken (i:plane W):Halo.BasisT d d (frown R Z Φ i) ((fresco R T Z Φ).main (Page.opening (signM M) i)):= (Z.depicts ..).1
lemma steered: Leading (fresco R T Z Φ):=fun w i r=> spinC _ _ _ (Φ w) (Z.tap w) (Z.accent w) (S.ε w) (S.hl _) i r
lemma sunny: CenterE (frown R Z Φ) S:=fun w _ _=> adheres Z.A (Φ w) (Z.tap w) (Z.accent w) _ _ _ (S.hl _)
-- full charge. finite root set union across steps

def bases (w:W) x:= Address.census (S.ε w) (Φ w).radius x
def cord (B: Finset Cover)(f: Side): Finset Cover:= B.image (fun x=> ((claims f).symm x).1)
def focuses (Φ:W→ PhaseTests d)(x:Room) : Page M→ Finset Cover := seriesC (X:=fun _=> Finset Cover) (fun w=>bases Φ (S:=S) w x) (fun i B=> cord B (R.steps i).patch.L)
lemma lowers {f:Side}{B:Finset Cover}(t:Site f) {z:Cover} (h:child f z t∈ B): z∈cord B f:= Finset.mem_image.mpr ⟨child f z t,h,congr_arg Prod.fst ((claims f).symm_apply_apply (z,t))⟩
lemma aligned (w:W)(x:Room){v:Cover}(hv:v∉bases (S:=S) Φ w x):sparks R T Z Φ (Page.opening M w) x v=0:=by
 rw [restore_start]; apply sum_eq_zero; intro i _; unfold partV framing
 have hp:0<S.ε w:= S.hl _
 have h:waveA i (S.ε w) (Φ w).phi (slide (S.ε w) v-x)=0:=by
    by_contra! hq; apply hv; apply (Address.enroll _ hp _ _ _).mpr; have hx := (Φ w).uses (in_ap i _ _ hq); change dist _ _ ≤ _ at hx;rwa [dist_eq_norm,sub_zero] at hx
 rw [h,mul_zero,zero_smul]
variable (K: Passage R) (hc:Common R)(hp:R.Follows T)(x:Room)
include K hc hp
lemma sites :∀ l :Page M,∀ v : Cover,v∉focuses R Φ x l → sparks R T Z Φ l x v=0:=by
 refine Page.proves (fun w i hi=> ?_) ?_
 · exact aligned R T Z Φ w x hi
 intro w hi v hv; rw [restore_step R T Z Φ K hc hp]; apply Finset.sum_eq_zero; intro j _; rw [hi, const_v]
 intro hu; apply hv; unfold focuses; rw [laterC]; exact lowers j hu
variable (G₀: Milieu S T k p L)
include G₀
lemma plaque : ∀ l i,i ≤ p → ((fresco R T Z Φ).main (leafX l x)) i= ∑ v∈focuses R Φ x l, sparks R T Z Φ l x v i:=by
 refine Page.proves (fun w i hi=> ?_) ?_
 · change (∑ t∈bases (S:=S) Φ w x, ∑ j:Stroke F, partV Z.A Z.origin Z.can (Φ w) (Z.tap w) (Z.accent w) (S.ε w) x t j) i= _
   rw [Finset.sum_apply]; apply sum_congr rfl;intro j _;rw [restore_start]
 intro w hi i hh; let A:= sparks R T Z Φ w.prev x; let B:= focuses R Φ x w.prev; let f:=(R.steps w).patch.L; let C:= focuses R Φ x w.next
 let Y:= (fresco R T Z Φ); let Q:= S.frames w
 change Y.main (turnX w x).next i= _; rw [← Y.step_m (turnX w x)]
 change (S.frames w).each d (T.bulk w.prev) ((fresco R T Z Φ).main (leafX w.prev x)) i=∑ v∈C, _
 rw [survivesP (V:=∑ v∈B,A v) _ _ (fun i he=> (hi i he).trans (Finset.sum_apply ..).symm) hh, dividends G₀ w (m:=d) B A (fun i _=> sparkCost R T Z Φ G₀ w.prev x i) hh]
 simp_rw [restore_step R T Z Φ K hc hp, Finset.sum_apply]
 let W(v:Cover):= Q.each d (T.bulk w.prev) (A v) i
 let V:=C×ˢ (Finset.univ : Finset (Site f))
 have hb:B ⊆ V.image (claims f):=by
    intro v ht; let P:= (claims f).symm v; refine Finset.mem_image.mpr ⟨P,mem_product.mpr ⟨?_,mem_univ _⟩,(claims f).apply_symm_apply v⟩
    unfold C focuses; rw [laterC]; exact Finset.mem_image.mpr ⟨_,ht,rfl⟩
 calc
    _= ∑ v∈ V.image (claims f),W v:=sum_subset hb (fun y _ ht=>by unfold W A; rw [sites R T Z Φ K hc hp x _ y ht,const_v]; rfl)
    _= ∑ v∈ V,W (claims f v):= Finset.sum_image (fun i _ j _ h=> (claims f).injective h)
    _= _:=(Finset.sum_product ..)

-- absolute restore at each tensor. infinite support over potentials, but after testing only finite root set BEFORE PSG.
lemma finance (l:Page M){i:ℕ}(hi:i≤p) (j:ℕ) (z: Tuple (Foot G) j) : (fresco R T Z Φ).main (leafX l x) i j z=∑' s:Cover,sparks R T Z Φ l x s i j z:=by
 rw [tsum_eq_sum (s:= focuses R Φ x l)];swap;exact fun i hi'=>by rw [sites R T Z Φ K hc hp x _ _ hi'];rfl
 rw [plaque R T Z Φ K hc hp x G₀ l i hi]; simp only [Finset.sum_apply]
end YM.RegulatorIR.Sources
