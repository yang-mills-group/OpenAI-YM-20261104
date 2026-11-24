import YM.Juniper.Bright.Light

/-!
# Periodic E model steps, the mixed lifted no-seed alphabet (I)

We do *not* lift the compulsory partners of the model. They have their
physical values in each input rep and their exact multipliers also occur in
flagged outputs. It suffices, in the selected high accuracy log calculation,
to lift **regular** exponents. This file extends the `Deck.Mint` calculation
to mixed words of arbitrary arity, whose additional letters are regular-E
vertices, not Penney/Mint. The primitive hypothesis on those letters is only
on the INPUT stencils (including support and value). Compare even where the
fine input isn't all-good. Coats use the actual physical masks and common
tag/Gaussian; no independent one per letter. This is for the kernel of the
step, before reset.

For projective natural templates, including the support of an old regular
entry in the template matters: identity merely on unmasked E sums would
not even pay the key footprint charge or yield the mask identity here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Mint Stellar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val}
    {Q : KernelChoices} {hC : C.val=c.val*M} {he : 2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {p : ℝ}
    {E : Forest (stepped Q h).ratio} {E' : Forest (stepped Q H).ratio}
    {X : Coat T E} {X' : Coat T' E'} (A : Stellar hC he K p X X')
    {R : RG.Rep G f} {R' : RG.Rep G F}
local notation "B" => radiusB p

/-- Only raw letters of these two types are projected. Needn't assert
 Charge equality or equal E choices for the world, even at same cut. -/
abbrev TypeLetter (c f : Side) := Music c f ⊕ ℕ
def sites (S : StepData c f) : TypeLetter c f ↪ Head S where
  toFun := Sum.elim (disc S) (Opacity.key S)
  inj' := by
    rintro (i|i) (j|j) h
    · exact congr_arg Sum.inl ((disc S).injective h)
    · change Mint.album S i=Opacity.key S _ at h
      rcases i with i|i|i|i <;> simp [Mint.album, Opacity.key, Mint.note] at h
    · change Opacity.key S _= Mint.album S j at h
      rcases j with j|j|j|j <;> simp [Mint.album, Opacity.key, Mint.note] at h
    · change Opacity.key S i= Opacity.key S j at h
      exact congr_arg Sum.inr (Sum.inl_injective (Sum.inl_injective (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))))

abbrev fanchor (R : Rep G f) (i : ℕ) := (R.activities.reg i).site
abbrev post (S : StepData c f) (R : RG.Rep G f) : TypeLetter c f → Site c :=
  Sum.elim (pace S) (S.ratio.parent ∘ fanchor R)

local notation "S" => stepped Q h
local notation "Y" => stepped Q H

/-- Primitive INPUT-lift of reg-E, no equations on its output.
 `value` only *inside* its actual mask. -/
structure Pair (W : Lace h H M) (R' : Rep G F) (R : Rep G f) (i j : ℕ) : Prop where
  sends : W.high.cut (fanchor R' i) = fanchor R j
  support : (R.activities.reg j).support=((R'.activities.reg i).support.image W.high.cut)
  value (U : Config G f) : Healthy R.p.threshold (R.activities.reg j).support U →
    R'.activities.E i (W.high.links U)= R.activities.E j U

variable {i j s t l B' : ℕ}
include hC he
lemma efoot (hP : Pair L R' R i j) (hg : f.val>4) :
    Raw.regularFoot (decreed h) l s R j=(Raw.regularFoot (decreed H) l s R' i).image (L).low.cut:= by
  let K':= L
  let Z := inspected (R'.activities.reg i).support
  unfold Raw.regularFoot enlargement
  rw [hP.support,(show inspected (image (L).high.cut _)=(Z.image K'.high.cut) from Deck.voyages (Deck.fineP h H hC) hg _), image_image]
  have hh : image ((decreed h).parent ∘ K'.high.cut) Z=
      image K'.low.cut (image (decreed H).parent Z):= by
    rw [image_image]; apply image_congr; intro k _
    exact Lace.position K' k
  rw [hh]; exact ringed hC _ _

lemma occurrence (hP : Pair L R' R i j) (hp : R'.p=R.p) (hg : f.val>4) (U : Config G f):
    R'.activities.regularOccurrence R'.p i ((L).high.links U) = R.activities.regularOccurrence R.p j U:= by
  unfold Activities.regularOccurrence; rw [hp]
  have hf : Healthy R.p.threshold (R'.activities.reg i).support ((L).high.links U) ↔ Healthy R.p.threshold (R.activities.reg j).support U := by
    rw [hP.support]; exact Deck.vigor (Deck.fineP h H hC) U hg R.p.threshold _
  by_cases hz : Healthy R.p.threshold (R.activities.reg j).support U
  · rw [masked_eq _ _ _ _ (hf.2 hz),masked_eq _ _ _ _ hz,hP.value U hz]
  rw [masked_ne _ _ _ _ (hf.not.mpr hz),masked_ne _ _ _ _ hz]

include A
lemma reg_read (hP : Pair L R' R i j) (hp : R'.p=R.p)
    (hg : 2*(t+3)<c.val)
    (w : Site C) (hw : Raw.regularFoot (decreed H) 0 (radiusB p) R' i ⊆ neighbors t w)
    (u : Directions G f) (a : ℝ) :
    X'.inhale R' a (Deck.light (L).high.cut u) (.inl i) = X.inhale R a u (.inl j) := by
  have he : 4<f.val := by
    have hm:= P.L.property; have hx:= A.old.buys
    have hh:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ hm; omega
  change -R'.activities.regularOccurrence R'.p i _ * X'.enforce (2*a) _ (X'.plaza (Raw.regularFoot (Y).ratio 0 X'.B R' i)) =
    -R.activities.regularOccurrence R.p j _ * X.enforce _ _ (X.plaza (Raw.regularFoot (decreed h) 0 X.B R j))
  rw [(A.glassU u).2.2, occurrence hP hp he (X.input u), A.D.1, A.D.2, efoot (l:=0) (s:=radiusB p) hP he]
  apply congr_arg
  exact A.porter (Raw.regularFoot _ 0 (radiusB p) R' i) t hg w hw (2*a) u

lemma grantedE (hP : Pair L R' R i j) (hp : R'.p=R.p) (hf : R'.beta=R.beta)
    (hg : 2*(t+3)<c.val) (w : Site C) (hw : Raw.regularFoot (decreed H) 0 (radiusB p) R' i ⊆ neighbors t w)
    (u : Air f G) (O : ChartRatio G) (Z a : ℝ) (k k' : Finset ℕ) :
    X'.vertex R' O Z a k l (blow (L) u) (Opacity.key (stepped Q H) i)= X.vertex R O Z a k' l u (Opacity.key (S) j):= by
  change Real.exp (X'.inhale R' a (X'.liftA R'.beta (blow _ u)) (.inl i)) -1= Real.exp (X.inhale R a (X.liftA R.beta u) (.inl j)) -1
  rw [hf, A.rolls, reg_read A hP hp hg w hw]


omit A hC he
def track (W : Lace h H M) (π : ℕ → ℕ) : TypeLetter C F → TypeLetter c f := Sum.map (verse_down W) π

/-- Chosen letter is either a short Music letter (the precise conditions of Deck)
 or an E letter paired under the template. -/
def Pertinent (W : Lace h H M) (π : ℕ → ℕ) (B' : ℕ) (R' : Rep G F) (R : Rep G f) : TypeLetter C F → Prop :=
    Sum.elim (fun i=> Mint.verse R'.path i ≤ B') (fun i=> Pair W R' R i (π i))

include hC he
lemma matched (π : ℕ → ℕ) (i : TypeLetter C F)
    (hp : R'.path=R.path) (hg : 4<f.val) (hh : Pertinent (L) π B' R' R i) :
    areas R T l s (sites S (track (L) π i))=(areas R' T' l s (sites Y i)).image (L).low.cut := by
  cases i with
  | inl i => exact (Stellar.voy (T:=T) (T':=T') i l s hp hg).2
  | inr i => exact efoot hh hg

include A
lemma pay (π : ℕ → ℕ) (i : TypeLetter C F) (hk : R'.path=R.path)
    (hp : R'.p=R.p) (hf : R'.beta=R.beta)
    (ht : Pertinent (L) π (radiusB p) R' R i)
    (w : Site C) (hw : areas R' T' l (radiusB p) (sites Y i) ⊆ neighbors t w) (hg : 2*(t+3)<c.val)
    (u : Air f G) (O : ChartRatio G) (Z a : ℝ) (k k' : Finset ℕ) :
    X'.vertex R' O Z a k l (blow (L) u) (sites Y i)= X.vertex R O Z a k' l u (sites S (track (L) π i)):= by
  cases i with
  | inl i => exact A.granted hk hp hf a u O i ht Z l k k'
  | inr i =>
    change Raw.regularFoot (Y).ratio l (radiusB p) R' i ⊆ _ at hw
    refine grantedE (T:=T) (T':=T') (R:=R) (R':=R') (l:=l) (i:=i) (j:=π i) A ht hp hf hg w ?_ u O Z a k k'
    apply Finset.Subset.trans _ hw
    unfold Raw.regularFoot enlargement; intro i hi; obtain ⟨j,h,hj⟩:= halo_spec.mp hi; apply halo_spec.mpr; exact ⟨j,h,hj.trans (by omega)⟩
omit A hC he

abbrev members (S' : StepData c f) (U : Finset (TypeLetter c f)):= U.map (sites S')
lemma no_seed (S' : StepData c f) (U : Finset (TypeLetter c f)) :
    (members S' U).toLeft=∅ ∧ Matter.own (members S' U)=∅ := by
  constructor <;> ext i
  · simp only [mem_toLeft,notMem_empty,iff_false]; intro hi; obtain ⟨j,hj,hx⟩:= mem_map.mp hi; cases j
    next j=> change album S' j= _ at hx; unfold Mint.album at hx; contradiction
    next j=> change Opacity.key S' j= _ at hx; unfold Opacity.key at hx; contradiction
  simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro hi
  obtain ⟨j,hj,hx⟩:=mem_map.mp hi; cases j
  next j=> change album S' j= _ at hx; unfold Mint.album at hx; injection hx with hf; contradiction
  next j=> change Opacity.key S' j= _ at hx; unfold Opacity.key at hx; injection hx with hf; contradiction
lemma no_roster (S' : StepData c f) (U : Finset (TypeLetter c f)):
    roster (members S' U)= ⟨∅,∅,∅⟩:= by unfold roster; rw [(no_seed S' U).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩ -- adapted from Mint
lemma troupers (S' : StepData c f) (T : Tube G S') (R : Rep G f) (U : Finset (TypeLetter c f)) (i j:ℕ) : troupe T R i j (members S' U):= by
  unfold troupe; rw [no_roster,(no_seed S' U).1,(no_seed S' U).2]; constructor
  · constructor
    · simp
    · simp
    simp [Packets.seeds]
  constructor <;> intro _ h <;> exact False.elim (notMem_empty _ h)
end YM.Juniper.Flare
