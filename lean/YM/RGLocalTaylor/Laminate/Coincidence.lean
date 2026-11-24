import YM.RGLocalTaylor.Laminate.Leaf
import YM.MergeProof.Wreath
import YM.RGLocalTaylor.Engine.Meaning

/-!
# All sources on the same kernel. `original` compatible with real Team evaluation,
 no factorization of an eligibility or covariance marker, and no relabelling of
 source footprints.
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March

namespace Laminate
open Mayer (original)
section set
variable (M : Team R)

-- exactly this catalogue through local tilts. For off-reach accesses only a dummy probe is needed.
abbrev chosen {A : Type*} (M : Team R) (S : StepData c f) (w : Leaf R → A) (fallback : Head S→ A) (u : Head S) : A:= if h : u∈M.signs S then
    w (Classical.choose (Finset.mem_image.mp (show u∈M.own.image (fun i=> i.turn.badge S) from h))) else fallback u

def partner (H : Cash W s μ L Q o C T R) (u : Head S) := chosen M S (power H) (fun _=> Insert.ofConst 1) u

def coverWeight (S:StepData c f) (u : Head S) := chosen M S Leaf.weight (fun _=>0) u

lemma distinct (S:StepData c f) : Set.InjOn (fun i : Leaf R=> i.turn.badge S) (M.own:Set _) := fun _ hi _ hj h=> M.alone hi hj (Team.badged S h)
lemma chosenAt {A:Type*} (S:StepData c f) (w : Leaf R → A) (fallback : Head S→ A) (u : Leaf R) (hu:u∈M.own) : chosen M S w fallback (u.turn.badge S) = w u:= by
  have he: u.turn.badge S∈ M.signs S:= mem_image_of_mem _ hu; unfold chosen; rw [dif_pos he]; apply congr_arg; exact distinct M S (Classical.choose_spec (mem_image.mp he)).1 hu (Classical.choose_spec (mem_image.mp he)).2
lemma coverTotal (S : StepData c f) : ∏ i∈ M.signs S, coverWeight M S i=M.weight:= by
  unfold Team.signs; rw [prod_image]; exact prod_congr rfl fun i hi=> chosenAt M S Leaf.weight (fun _=>0) _ hi; exact distinct M S
variable {M} {p : Molecule S}
lemma partnerFit {i:Head S} (he:i∈ M.signs S): Fits H (partner M H i) (H.supportP i) j ∧ 0≤coverWeight M S i:= by
  obtain ⟨i,hi,rfl⟩:=mem_image.mp he; unfold partner coverWeight; rw [chosenAt M _ _ _ _ hi,chosenAt M _ _ _ _ hi]; exact ⟨power_fit .., i.profit⟩
lemma support_eq {i : Head S} (he:i∈ M.signs S) : blaze ({i}:Molecule S)=∅:= let ⟨i,_,h⟩:= mem_image.mp he; h ▸ wingSafe i -- syntax
lemma fit_original (p:Molecule S) : Fits H (original H p (p\M.signs S) (partner M H)) (H.unionP p) j := by
  unfold Mayer.original; apply Fits.joined; intro i hi; apply Fits.bigger (u:=H.supportP i) _ (subset_biUnion_of_mem _ hi)
  split; exact fits_leg ..; next h=> exact (partnerFit (Classical.byContradiction (fun he=> h (mem_sdiff.mpr ⟨hi,he⟩)))).1
lemma into_coins (he:M.signs S ⊆ p) (hX:X.x=s) (ha:X.manifest) (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (v : F.Slice G × Air f G):
    M.into X W o.a Q.table (own p) Q.halo p v = (original H p (p\M.signs S) (partner M H)).joint X v:= by
  unfold Team.into Team.premium; rw [if_pos he]
  let A:=X.wrapY v.1; let u:=v.2; let Z(i):= if i∈ p\M.signs S then leg H (own p) i else partner M H i
  have hv':Room P S T A.x:= hX.symm ▸ H.laws.data.room
  have ht : worldZ A R.beta u=A.liftA R.beta u:= (shine A hv' ha _ _).symm
  change M.paidU A o.a (A.liftA R.beta u) * A.term _ _ _ _ _ _ u _= ∏ i∈p,(Z i).value A u
  rw [← prod_sdiff he,mul_comm]
  apply congr_arg₂ (·*·)
  · unfold Coat.term; apply prod_congr rfl; intro i hi; unfold Z; rw [if_pos hi]; refine whereBorn A o.a R W Q.table u (own p) hv' ha Q.buys i ?_
    have h : Healthy (Pressure.temp s) (H.supportP i) X.V := Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP ((mem_sdiff.mp hi).1)) hy
    unfold Coat.B;rw [show A.x=s from hX]; exact h
  unfold Team.paidU Team.signs; rw [prod_image]; apply Finset.prod_congr rfl
  · intro i hi; unfold Z partner; rw [if_neg (show i.turn.badge S ∉ p\M.signs S from (fun h=> (mem_sdiff.mp h).2 (mem_image_of_mem _ hi))),chosenAt M _ _ _ _ hi]; dsimp only [power]; rw [ht]
  exact distinct M S

lemma teamLecturer (he:M.signs S ⊆ p) (U:Config G c) (N:Captain H j C' d v Y A b r B q n χ) (hV:(roster p).flags=∅) :
    M.lotus T s χ o.K W o.a Q.table Q.halo U p=masked (Pressure.temp s) (H.unionP p) ((original H p (p\M.signs S) (partner M H)).onLog H χ p) U:= by
  let Ω:= original H p (p\M.signs S) (partner M H); let X (u:Greenbelt.Reserve S):= Greenbelt.prism T s χ o.K U (allot u); let Z (u:Greenbelt.Reserve S)(k:S.Choices):= (planted (X u) p).taggedL k
  have hx (u:Greenbelt.Reserve S): standsIn (X u) R Q.halo p ↔ authorized H p ∧ Healthy (Pressure.temp s) (H.unionP p) U:= by
    unfold standsIn claimed;rw [hV,inter_comm,← disjoint_iff_inter_eq_empty]; exact and_assoc.symm
  by_cases hp : Healthy (Pressure.temp s) (H.unionP p) U
  swap; · rw [masked_ne _ _ _ _ hp]; unfold Team.lotus; simp only [likely]; rw [sum_eq_zero,mul_zero]; exact fun i _=> if_neg (fun h=>hp (((hx i).1 h).2))
  rw [masked_eq _ _ _ _ hp]; unfold Team.lotus; by_cases hz:authorized H p
  swap; · rw [Insert.onLog_of_forbidden hz, likely,sum_eq_zero, mul_zero]; exact fun i _=> if_neg (fun h=>hz (((hx i).1 h).1))
  rw [(fit_original (M:=M) (H:=H) (j:=j) p).exact_meaning (N:=N) U hz hV hp]; apply congr_arg likely; funext u; unfold Team.bloom; rw [if_pos ((hx u).2 ⟨hz,hp⟩)]; unfold Team.steep; apply congr_arg likely; funext t
  exact congr_arg (fun f=>∫ y,f y ∂Insert.moment (Z u t)) (funext (into_coins (X:= Z u t) he rfl (planted_valid (X u) p) hp))
end set
end Laminate
end YM.RGLocalTaylor
