import YM.LocalTaylorR2.Orbit.Crews
import YM.MergeProof.TeamWorld
/-! Represent the exact finite Team entry at the unmasked-Healthy polynomial. Uses Cohort identities; no a priori prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
abbrev restP:= (Θ) \ (M.signs S)

def hero : Port.Test T:= fun _ X w=> M.paidU X o.a (worldZ X R.beta w)* Polar.floating X o.a R W Q.table w (own Θ) Q.halo (restP M H p)
-- Set paid even if not authorized.Still no Spark membership: oath
lemma honor (h:Ω⊆Θ): Kept H (H.smallAt p) (fun _ X w=> M.paidU X o.a (worldZ X R.beta w)):= Kept.product M.own (fun i:Leaf R=> Marker.stems i H) (fun i hi=> (Marker.stemTest i H).mono (Finset.subset_biUnion_of_mem H.supportP (h (Finset.mem_image_of_mem _ hi)))) -- args
lemma hero_test (h:Ω⊆Θ):Kept H (H.smallAt p) (hero M H p):= by
  exact (honor M H p h).times (Kept.product (restP M H p) _ (fun j hj=> (crews H (own Θ) j).mono (Finset.subset_biUnion_of_mem H.supportP ((Finset.mem_sdiff.mp hj).1))))
  -- f alignment
-- replace native term
variable (hx:X.x=s)(hk:X.width=o.K)
include hx hk
local notation "HG"=> (H.unionP p.val)
open Rotation
lemma heroine (hm:X.manifest)(h:Ω⊆Θ)(hu: Healthy (Pressure.temp s) HG X.V) :
    Port.average X (podium S G HG X.B) (hero M H p)= M.tithe X (own Θ) W o.a Q.table Q.halo Θ:=by
  let B:=podium S G HG X.B; have H':Cash W X.x μ L Q o C T R:= hx.symm ▸ H
  -- DON'T use independently given H' for support; H'.supportP definitional? cash index from T same hx; yes
  have hR : X.relating.PosDef := (H.laws.data.localP _ X hx hk hm).sails.fullC
  have hv : (circuit B X.relating).PosDef:= hR.submatrix Subtype.val_injective
  have ht:= H.laws.intake; have hp:= hx.symm ▸ ht
  have he : Room P S T X.x:= hx.symm ▸ H.laws.data.room; let I:=own (Θ)
  have hr: Healthy (Pressure.temp X.x) (ground R T Q.halo X.B Θ) X.V:=by unfold Coat.B; rw [hx]; exact hu
  have hh := M.tip X I H' hk hm Θ
  unfold Port.average Team.tithe; rw [integral_prod _ hh.2.1]; apply integral_congr_ae; filter_upwards with y
  let g (z : Air f G):= M.into X W o.a Q.table (own Θ) Q.halo Θ (y,z)
  have hp : Measurable g:= hh.1.meas.comp (measurable_const.prodMk measurable_id)
  let Y:= X.wrapY y; have hz z: hero M H p F Y z=g z:=by
    unfold hero g Team.into Team.premium; rw [if_pos h,show worldZ Y R.beta z=Y.liftA R.beta z from (shine Y he hm _ _).symm];
    exact congr_arg (_*·) (Polar.afterborn Y o.a R W Q.table z (own Θ) he hm Q.buys (restP M H p) (Finset.disjoint_of_subset_left (Finset.biUnion_subset.mpr (fun i hi=> subset_biUnion_of_mem _ ((Finset.mem_sdiff.mp hi).1))) hr)).symm
  symm; change (∫ i, g i ∂ _)=_; refine Eq.trans ((Pond.gathered (Pond.spill B) (Pond.spill_m B) (Pond.orbit hR.posSemidef B) (Pond.settled _) (f:=g) ?_ hp).trans (Shield.recommends _ hv (fun z=>g (spill B z)))) ?_
  swap; · exact integral_congr_ae (Eventually.of_forall fun z=>congr_arg (_*·) (hz _).symm)
  intro u v h
  let W:= (H.unionP Θ)
  refine M.concur Y _ _ ⟨Village.refl Y W,(Pond.observe B).1 h,fun _ _=>Iff.rfl⟩ he Q.buys ?_ (show Intake P T X.x R from hx.symm ▸ H.laws.intake)
  change ground R T Q.halo (radiusB X.x) Θ⊆ (H.unionP Θ)
  rw [hx]; exact Subset.refl _

abbrev checked : Prop:= vetted H p ∧ Ω ⊆ Θ
local notation "vθ"=> hero M H p
lemma charged_here (h:checked M H p) (hu:Healthy (Pressure.temp s) HG X.V): M.bloom X W o.a Q.table Q.halo Θ=onFrame X Θ HG vθ:=by
  have hp:(roster Θ).flags=∅:= p.2.2; unfold Team.bloom onFrame; rw [if_pos ?_];
  · apply congr_arg likely; funext j
    let Y:=(planted X Θ).taggedL j; rw [← show _=M.tithe Y (own Θ) W o.a Q.table Q.halo Θ from heroine M Y H p hx hk (planted_valid X Θ) h.2 hu]
    have hh := plantedRule X hx hk (hero_test M H p h.2) Θ X.V hu hp j
    rw [show Y.B=radiusB s from congr_arg radiusB hx,show X.B=radiusB s from congr_arg radiusB hx]; exact hh
  have ht : ground R T Q.halo X.B Θ=HG:= by unfold Coat.B; rw [hx]; rfl
  have hx' : RG.flags (Pressure.temp X.x) X.V ∩ ground R T Q.halo X.B Θ=(roster Θ).flags:=by rw [ht,hx,hp]; exact Finset.disjoint_iff_inter_eq_empty.mp (show Disjoint _ _ from hu.symm)
  unfold standsIn claimed; rw [show X.B=radiusB s from congr_arg radiusB hx] at hx' ⊢
  exact ⟨h.1.1,h.1.2,hx'⟩
lemma tasted (h:checked M H p) (hu: Healthy (Pressure.temp s) HG X.V): M.bloom X W o.a Q.table Q.halo Θ=rinsed X Θ HG vθ:=by
  symm; unfold rinsed; have he : ∀ z:Site c→G.El,onFrame (X.rinse z) Θ HG vθ= M.bloom X W o.a Q.table Q.halo Θ:=by
    intro z; refine (charged_here M (X.rinse z) H p hx hk h ?_).symm.trans (M.radian X (hx.symm ▸ H) hk Θ z)
    change Healthy _ _ (gauge _ _); unfold Healthy; rw [gauge_flags]; exact hu
  simp_rw [he]; rw [integral_const]; simp

omit hx hk
abbrev deck (V:Config G c):= if checked M H p then episode H χ Θ vθ V else 0
local notation "W!" => deck M H χ p
-- note deck isn't a change of contour. its unmasked support & weights matter.
include hx in
private lemma sane (he : M.bloom X W o.a Q.table Q.halo Θ≠0) : checked M H p ∧ Healthy (Pressure.temp s) HG X.V:=by
  have hf: Ω⊆Θ:= Classical.byContradiction fun h=> he (M.bloom_off X Θ h)
  unfold Team.bloom at he; split at he
  next ht=>
    obtain ⟨h₁,h₂,h₃⟩:=ht; have hB:X.B=radiusB s:=congr_arg radiusB hx; rw [hB] at h₁ h₂ h₃; have hu:=p.2.2; rw [hx,hu,inter_comm] at h₃; exact ⟨⟨⟨h₁,h₂⟩,hf⟩,disjoint_iff_inter_eq_empty.mpr h₃⟩
  exact False.elim (he rfl)
lemma dose (V:Config G c): M.lotus T s χ o.K W o.a Q.table Q.halo V Θ = masked (Pressure.temp s) (H.smallAt p) W! V :=by
  rw [show H.smallAt p=HG from rfl]
  let X i:= prism T s χ o.K V (Greenbelt.allot i)
  by_cases h: checked M H p ∧ Healthy (Pressure.temp s) HG V
  · rw [masked_eq _ _ _ _ h.2,deck,if_pos h.1]; exact congr_arg likely (funext fun i=> tasted M (X i) H p rfl rfl h.1 h.2)
  letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  have hp : ∀ i:Greenbelt.Reserve S,M.bloom (X i) W o.a Q.table Q.halo Θ=0:= fun i=> Classical.byContradiction fun hz=> h (sane M (X i) H p rfl hz)
  change likely (fun i=> M.bloom (X i) _ _ _ _ _) =_
  simp_rw [hp]; rw [Greenbelt.likely_constant]; by_cases he : Healthy (Pressure.temp s) HG V
  · rw [masked_eq _ _ _ _ he,deck,if_neg (fun hp=> h ⟨hp,he⟩)]
  rw [masked_ne _ _ _ _ he]
end YM.LocalTaylorR2.Orbit
