import YM.LocalTaylorR2.LogTest
import YM.LocalTaylorR2.Germ
import YM.LocalTaylorR2.Series
import YM.RG01.Survive.Leaves

/-!
# Retain this log alphabet

Retaining an inherited E input holds it *exact*. This Taylor expansion in
log perturbation applies without any compatibility with a formal g-independent
operator -- for example these are cutoff-dependent masked germs, no unmasking
and no directed recursion is asserted. Every term of the polynomial through
degree p is computed independently of the output. Reserve error includes
all non-retained heads. Pairs (long-path remainder) and ChainIndex may be
discarded as well as warnings, without dropping their actual small/forced
occurrences (which are charged, including derivatives).
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port RG01.Survive PhysicalNext PhysicalNext.Repeat Greenbelt
variable {k : ℕ} {p : Molecule S}

def slowRaw (c f : Side) : Raw.LogLetter c f → ℕ := Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (fun _=>1))))
def slowLog (c f : Side) : LogIndex c f → ℕ := Sum.elim (slowRaw c f) (Sum.elim (fun _=>0) (fun _=>1))

def logs (p : Molecule S) : Finset (LogIndex c f) := p.toRight.toRight.toLeft
lemma log_occ (i:LogIndex c f) : i∈logs p↔ identityLog i∈p := by simp [logs, identityLog]
-- Do not run any estimate only for Pure. all polluted molecules must be charged too

def Deer (i : Head S) : Prop := ∃ q, identityLog q=i
def Drain (i : Head S) : Prop := ∃ q, identityLog q=i ∧ slowLog c f q=0
def Pure (p:Molecule S) := ∀ i∈p,Deer i
def Clear (p:Molecule S) := ∀ i∈p,Drain i
lemma isPure (h:Clear p):Pure p:=fun i hi=> Exists.imp (fun _=>And.left) (h i hi)
lemma scenic_inj : Function.Injective (identityLog (S:=S)) := by intro i j h; simpa [identityLog] using h
lemma allPure (h:Pure p): p=(logs p).image identityLog := by
  ext i; rw [mem_image]
  constructor
  · intro hi; obtain ⟨q,rfl⟩:= h i hi; exact ⟨q,(log_occ q).2 hi,rfl⟩
  rintro ⟨q,hq,rfl⟩; exact (log_occ q).1 hq
lemma forestCard (h:Pure p) : p.card=(logs p).card :=by
  exact (congr_arg Finset.card (allPure h)).trans (card_image_of_injective _ scenic_inj)
lemma subsetCard (p:Molecule S): (logs p).card≤ p.card:=by
  rw [← card_image_of_injective _ (scenic_inj (S:=S))]
  refine Finset.card_le_card fun i hi=> ?_
  obtain ⟨i,he,rfl⟩:= mem_image.mp hi; exact (log_occ i).1 he

abbrev Paint (p : Molecule S) (k:ℕ):= ↥(logs p)→Series.Letter k
def inserts (q:Paint p k) : ℕ := ∑ i,Series.rank (q i)
variable (H)
def compound (p : Molecule S):Port.Test T := fun F X w=> ∏ i ∈ logs p, Series.mellow (weightLog H i F X w)
def letters (q:Paint p k) : Port.Test T := fun F X w=> ∏ i : ↥(logs p), Series.split (q i) (weightLog H i.val F X w)

lemma compSect (p:Molecule S): Kept H (H.unionP p) (compound H p) := by
  apply Kept.product
  intro i hi; exact ((logTest H i).mono (subset_biUnion_of_mem H.supportP ((log_occ i).1 hi))).smooth _ (Real.contDiff_exp.sub contDiff_const)
lemma letterSect (q:Paint p k) (U : Support c) (h:H.unionP p ⊆ U): Kept H U (letters H q) := by
  apply Kept.product
  intro i hi; exact (((logTest H _).smooth _ (Series.smooth (q i))).mono ((subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans h))
lemma running (k:ℕ)(F:Tree.Forest S.ratio)(X:Coat T F)(w:Air f G): compound H p F X w=∑ q:Paint p k, letters H q F X w:=by
  unfold compound; rw [← prod_attach (logs p)]
  simp_rw [Series.allLetters k]; exact Fintype.prod_sum (f:=fun i:↥(logs p)=>fun q:Series.Letter k=> Series.split q (weightLog H i.val F X w))

lemma test_eq (s:Finset ℕ) (h:Pure p)(X:Coat T F) (w:Air f G): compound H p F X w=Polar.floating X o.a R W Q.table w s Q.halo p:=by
  unfold Polar.floating
  conv_rhs => arg 1; rw [allPure h]
  rw [prod_image (fun _ _ _ _ he=>scenic_inj he)]; exact prod_congr rfl fun _ _=>rfl

lemma leafEq {i:H.ThinP} (h:Pure i.val) (he : Ac.Spark H.supportP i.val) (hp : troupe T R Q.halo (radiusB s) i.val)
    (χ:Chi) (V:Config G c) : leaflet H χ V i=episode H χ i.val (compound H i.val) V :=by
  apply congr_arg likely; funext j
  apply integral_congr_ae; filter_upwards with z
  let X:=(prism T s χ o.K V (Greenbelt.allot j)).rinse z; change shelter X W o.a i.val R Q.table Q.halo =onFrame X i.val (H.unionP i.val) _
  rw [shelter,if_pos ⟨he,hp⟩]; apply congr_arg likely; funext k
  unfold Port.average bars; simp_rw [test_eq H (own i.val) h]; rfl
end YM.LocalTaylorR2
