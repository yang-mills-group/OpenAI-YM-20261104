import YM.RGLocalTaylor.Mayer.Full
import YM.RGLocalTaylor.Engine.Meaning

/-!
# Interpretation as joint Haar/Gaussian local moments

Expose kernels AFTER Taylor expansion and BEFORE clustering. This is also a
uniform scalar/coordinate derivative premise (not an adaptive read based on
post-computed local answer). We work at *all* fixed fields locally eligible at
a real sector label; V is not globally restricted, the Laws are rather those
of the tour / with port `Passes` fees. Not changing representation to
compare kernels off-mask (formula might extend by its seam there).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
namespace Mayer
open Insert
variable {p select : Molecule S} {M : ℕ} (u : Decors select M) {K θ e uJ vJ discount : ℝ}
    (hs : select⊆p) (hw : decorOrder u ≤ M)

/- Mandated formula *even while pairing with marked sources*. -/
def exponent (_H : Cash W s μ L Q o C T R) (X : Coat T F) (w : Air f G) (i : Head S) := match i with
    | Sum.inr (.inr (.inl i)) => X.farLog R o.a Q.table w i
    | _ => 0

def planned (H : Cash W s μ L Q o C T R) (p : Molecule S) (u : Decors select M)
    (f' : Head S → Insert T) (X : Coat T F) (z : momentSpace X) := (∏ i ∈ p\select, (f' i).joint X z) *
      ∏ i:↥select,(exponent H (X.wrapY z.1) z.2 i.val)^((u i).val+1)/ ((u i).val + 1).factorial

variable (N : Captain H j C' d v Y A b r B q n χ) (hG : Awning H N.conduit A b discount e uJ vJ k l)
    (hg : Q.goal L s ≤ K) (hT : Approved K θ j M)
    (f' : Head S → Insert T) (hf : ∀ i∈p\select, Fits H (f' i) (H.supportP i) j)
    (hp : Start select) (hh:Healthy (Pressure.temp s) (H.unionP p) X.V) (he : (roster p).flags=∅)
    (hA : authorized H p) (hX : X.x=s) (hK : X.width=o.K) (hχ : X.χ=χ) (hM:X.manifest)

include hs hw hp N hG hg hT hh hX hK hM hχ
lemma physical_plan : (tagged H p f' u).joint X = planned H p u f' X := by
  funext z; unfold joint; unfold tagged Insert.joined planned; dsimp only
  rw [← prod_sdiff hs]; refine congr_arg₂ (· * ·) ?_ ?_
  · exact prod_congr rfl (fun i hi=> by simp only [payload,dif_neg (mem_sdiff.mp hi).2]; rfl)
  rw [← prod_attach select]; refine prod_congr rfl ?_
  rintro ⟨i,hi⟩ _; unfold payload; rw [dif_pos hi]
  obtain ⟨a,rfl⟩:= hp i hi
  let o':Fin M:=⟨_,decorOrder_lt hw ⟨badge S a,hi⟩⟩
  exact (realizes (X:=X.wrapY z.1) hG hT hg N.position.le (own p) z.2 a hX hK hχ hM (Finset.disjoint_of_subset_left
    (subset_biUnion_of_mem _ (hs hi)) hh) o').1 -- compatibility after cast

include hf
lemma integrable_planned : Integrable (planned H p u f' X) (moment X) := by
  rw [← physical_plan u hs hw N hG hg hT f' hp hh hX hK hχ hM]; exact (fits_tagged H f' hf u).onMoment (N:=N) hX hK hχ hM

include hA he
omit hh hX hK hχ hM
lemma localized (V : Config G c) (hv:Healthy (Pressure.temp s) (H.unionP p) V) :
    (tagged H p f' u).onLog H χ p V=likely fun i:Greenbelt.Reserve S=>likely fun j:S.Choices=>
      let X:= ((planted (prism T s χ o.K V (Greenbelt.allot i)) p).taggedL j)
      ∫ z, planned H p u f' X z ∂moment X:= by
  rw [(fits_tagged H f' hf u).exact_meaning (N:=N) V hA he hv]
  have hΩ (a b:Fintype (Greenbelt.Reserve S)) (f g : Greenbelt.Reserve S → ℝ) (h:f=g):@likely _ a f = @likely _ b g := by rw [Subsingleton.elim a b,h]
  apply hΩ; funext i; refine congr_arg (@likely S.Choices _) ?_; funext j
  let Y:= prism T s χ o.K V (Greenbelt.allot i); let X:= (planted Y p).taggedL j
  exact congr_arg (fun q=> ∫ z, q z ∂moment X) (physical_plan (X:=X) u hs hw N hG hg hT f' hp hv rfl rfl rfl (planted_valid Y p))

-- In particular can plug it into the retained portion of the unforced-density Taylor
-- model without approximation, at every locally unflagged point.
omit hp hA he u hs hw hf
lemma meaning_release {p : H.ThinP} {m : ℕ} (hw:m ≤ M) (V : Config G c) (hh:Healthy (Pressure.temp s) (H.smallAt p) V)
    (hp : Start p.val) (ha : authorized H p.val) : issue H χ M p (Fin.castSucc (⟨m,Nat.lt_succ_of_le hw⟩ : Fin (M+1))) V =
    ∑ g∈univ.filter (fun g:Decors p.val M=> decorOrder g=m),
      likely fun i:Greenbelt.Reserve S=>likely fun j:S.Choices=>
        let X:= ((planted (prism T s χ o.K V (Greenbelt.allot i)) p.val).taggedL j)
        ∫ z,planned H p.val g (leg H (own p.val)) X z ∂moment X:= by
  unfold issue atLeaf; simp only [Fin.val_castSucc]; rw [if_neg (show ¬m=M+1 by omega), if_pos hp]
  exact sum_congr rfl fun i hi=> localized i (Finset.Subset.refl _) ((mem_filter.mp hi).2.symm ▸ hw) N hG hg hT _ (by simp) hp p.2.2 ha V hh
end Mayer
end YM.RGLocalTaylor
