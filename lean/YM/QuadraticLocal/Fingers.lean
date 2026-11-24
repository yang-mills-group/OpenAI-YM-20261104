import YM.QuadraticLocal.Canopy
import YM.RemainderComparison.Encore.Banner
/-!
## Input/admission side: purchasing test-uniform Lyric hypotheses

From FULL Gallery for each fixed mark capacity, not just startup cylinders.
Use Θ and restriction to supported words; no perturbative rank limit involved yet. Convert to
PORTRAIT as a catalog of (possibly MANY marks & interactions & test stencils); as much grouping
into the vacuum log as has actually been done by reclosure, with E routes assigned to the true
slot reservoir. Although Roots alone are enough to purchase Scale, stencil identities can inspect
every route chosen here. Number of names/Θ does *not* enter* the price—even if one torus family
contains millions of zero/far-away keys. Uses real/imag split, two unit rays on each nonzero mark
word, with **sup envelope paid first**. For a complex test protocol, this does NOT assert
complex multilinearity for each raw split half. Bind with extra ℝ-protocol (or use as Lyric input
but publish re-summed/complex-linear projection at polynomial output; later).

No setup budget from declaring representations after test queries. Keep larger hit exponent for
this input than `radiusCost` minimum if needed. Requires *output previous* soft and K masks and
representation at actual P, exact p, including extra predicate, and chosen K & E decompositions.
Purchase `crown` in `Scale` using already given Hit (no occupancy issue on fine input names;
its dummy grouping array in this battery uses *fine sites*, not markers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Trigger
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Lotus Merge Palette
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse RemainderComparison.Mosaic RemainderComparison.Serif RemainderComparison.Typeface
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}{n c:Side}{P : Rep G n}{V:Type}[DecidableEq V]{R:Census V}{o:V→Site n}{f α β k a b d r s c' :ℝ}
variable {T:Type*}{I:Type}[Countable I] (A:Gallery T I o P R) (S:StepData c n)
set_option quotPrecheck false
local notation "p"=> P.p
local notation "X"=> P.activities
def Origins {V n}{o:V→Site n} (t:Support n)(i:Finset V): Prop:= ∀ v∈i,o v∈t
abbrev Fires := {i : I // ¬ A.E.clear i}
abbrev Fog (Z:ℕ→ Support n)(R:Census V)(o:V→ Site n):= { i:ℕ× R.Mode // i.2≠ R.quiet ∧ Origins (o:=o) (Z i.1) i.2.val }
local notation "Fog0"=> Fog (fun i=>(P.activities.forced i).support) R o
abbrev Table := (Fires A) ⊕ (Fog (fun i=>(P.activities.forced i).support) R o)
def status : Table A → R.Mode := Sum.elim (fun i=> A.E.mode i.val) (fun i=> i.val.2)
omit [Countable I] in
lemma status_hot (i:Table A): status A i ≠ R.quiet:= by cases i; exact A.E.live _; exact ‹Fog0›.prop.1
-- entries before real stamps on exactly those addresses. z ← Bool × Table A
local notation "J"=> Table A
local notation "J₁"=> J × Bool

variable (w:V→ℝ)
def slice : Bool→ ℂ→ℝ | false=> Complex.re | true=> Complex.im
def lens : Bool→ℂ| false=>1|true=> Complex.I
lemma tone_size (b:Bool):‖lens b‖=1:=by cases b<;> simp [lens]
lemma slice_cost (b:Bool)(v:ℂ):‖slice b v‖≤‖v‖:=by cases b; exact Complex.abs_re_le_norm v; exact Complex.abs_im_le_norm v
@[fun_prop] lemma slice_cont (b:Bool): Continuous (slice b):=by cases b; exact Complex.continuous_re; exact Complex.continuous_im
local notation "W"=> Poly.toll w
variable (hw:∀ i,0<w i)
def axis (i:J₁) := Poly.send (status A i.1) ((↑((Poly.toll w (status A i.1))⁻¹):ℂ)* lens i.2)
include hw
omit [Countable I] in
lemma choir (k:ℕ) (hk:∀ i:R.Mode,i.val.card≤k) : Chorus R w Set.univ (axis A w) k:= by
  apply production (axis A w) w Set.univ hw _ _ k hk
  · intro i; ext1 t; unfold axis; rw [Poly.part_mul,Poly.part_nil]; refine sum_eq_zero fun j _=>sum_eq_zero fun y _=>?_
    rw [Poly.part_send,Poly.part_send]; split_ifs with h' hA hB <;> simp_all only [mul_zero,zero_mul]
    exfalso; have he := status_hot A i.1; exact he (Subtype.ext (disjoint_self.mp h'.1))
  intro i _; unfold axis; rw [Poly.solo, Poly.part_send]; rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (Poly.worth hw _).le), tone_size,mul_one,mul_inv_cancel₀ (Poly.worth hw _).ne',if_neg (status_hot A i.1).symm]; simp
omit hw
omit [Countable I] in
lemma chop_carried (i:ℕ) (t:T) (U:Config G n)(j:R.Mode)(hp: ¬ Origins (o:=o) ((X).forced i).support j.val): (A.K.hard t i U).part j=0:=by by_contra h; exact hp ((A.K.locality t i).carry U _ h)

def viewE (t:T)(i:Fires A) (U:Config G n):ℂ:= A.E.light t i.val U
def color (i:J) (t:T) : Config G n → ℂ := i.elim (fun j=> viewE A t j) (fun i=> fun U=> (A.K.hard t i.val.1 U).part i.val.2)
def conn (i:Fires A)(r:Bool):ℕ:= blankRow n (A.E.address i.val,Extra.Trajectories.pin (i,r))
def wing (i:J₁): Wing:= i.1.elim (fun j=> Wing.logKey (conn A j i.2)) (fun j=>Wing.gasKey j.val.1)

lemma conn_inj {i j:Fires A}{b c:Bool}(h:conn A i b=conn A j c): (i,b)=(j,c):= Extra.Trajectories.pin_injective (congr_arg Prod.snd ((blankRow n).injective h))
variable (H: HasSlots P.p P.activities)
include H
lemma connE (i:Fires A× Bool): (X).reg (conn A i.1 i.2)= A.E.address i.1.val:=by rw [H.reg]; unfold conn drawer blankRow; simp only; rw [recorded]
lemma wingE (j:J)(b:Bool): (wing A (j,b)).support P= j.elim (fun i=> A.E.ground i.val) (fun i=> ((X).forced i.val.1).support):=by
    cases j; rename_i j; change ((X).reg (conn A j b)).support= _; rw [connE A H (j,b)]; rfl
    rfl
lemma roots (i:J₁): Origins (o:=o) ((wing A i).support P) ((status A i.1).val):=by
   rcases i with ⟨i|i,b⟩
   · rw [wingE A H]; exact A.E.roots _
   rw [wingE A H]; exact i.prop.2
-- Let Promises expose sup values to Portrait. enough for Tempo.Lyric
variable (g:I→ℝ)(d:ℕ→Poly R)
variable (hE:∀ i (t:T) (U:Config G n), ‖A.E.light t i U‖ ≤ g i)(hF:∀ i t U, Width.Covered (A.K.hard t i U) (d i))

def cape (i:J):ℝ:= W (status A i)* (i.elim (fun i=> g i.val) (fun i=> ‖(d i.val.1).part i.val.2‖))
def realValue (i:J₁)(t:T)(U:Config G n):ℝ:= W (status A i.1)*slice i.2 (color A i.1 t U)

include hF hw hE
lemma shapes (i:J₁)(t:T): UsesFinal (p).threshold ((wing A i).support P) (realValue A w i t) ∧ (wing A i).blank P ∧ (∀ U, realValue A w i t U≠0→(wing A i).qualifies P U) ∧ (∀ U, ‖realValue A w i t U‖≤ cape A w g d i.1) ∧ Measurable (realValue A w i t) ∧ GaugeInvariant (realValue A w i t):=by
    let b:= i.2; let v:= W (status A i.1); have hp :0<v:= Poly.worth hw _
    let F:=color A i.1 t; let u:= wing A i
    have hF₀:UsesFinal (p).threshold (u.support P) F∧ u.blank P∧(∀ U,F U≠0→u.qualifies P U) ∧ Measurable F∧ GaugeInvariant F:=by
       rcases i with ⟨i|i,b'⟩
       · let u:=A.E.ground i.val; let f:= masked (P.p.threshold) u (A.E.nominal t i.val); let j:=conn A i b'; let he:= A.E.legal t i.val
         have hx: color A (.inl i) t=f:=by funext U; unfold color viewE Lamps.light; dsimp only [Sum.elim_inl]; rw [if_neg i.property]
         have hv x: Wing.qualifies (Wing.logKey j) P x= Healthy P.p.threshold u x:= by change Healthy _ ((X).reg j).support _ =_; rw [connE A H (i,b')]; rfl
         have hh : GaugeInvariant f:= by
            intro z U; let V := Lattice.gauge z U; have hx : Healthy (P.p.threshold) u V ↔ Healthy (P.p.threshold) u U:=by unfold Healthy V; rw [gauge_flags]
            unfold f; by_cases h:Healthy (P.p.threshold) u U
            · rw [masked_eq _ _ _ _ (hx.mpr h), masked_eq _ _ _ _ h, he.symmetry]
            rw [masked_ne _ _ _ _ (mt hx.mp h), masked_ne _ _ _ _ h]
         change UsesFinal _ _ (color A (.inl i) t) ∧ _ ∧ (∀ U,color A (.inl i) t U≠0→ _) ∧ Measurable (color A (.inl i) t) ∧ GaugeInvariant (color A (.inl i) t); rw [hx]; refine ⟨?_,H.regular _,fun U h=>?_ ,(masked_measurable _ _ _ he.borel),hh⟩
         · have ho:UsesFinal (p).threshold u f:=by
             intro U V hu ht; have hv' : Healthy (p).threshold u U↔Healthy (p).threshold u V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,ht]
             unfold f; by_cases hp:Healthy (p).threshold u U; rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ (hv'.mp hp)]; exact he.sites U V hu; rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ (mt hv'.mpr hp)]
           rw [wingE A H]; exact ho
         change Wing.qualifies (Wing.logKey j) P U; rw [hv]; exact not_not.mp fun hx=> h (masked_ne _ _ _ _ hx)
       let h:= A.K.locality t i.val.1; let l':=i.val.2
       refine ⟨fun U V hu ht=> congr_arg (fun x:Poly R=> x.part l') (h.reads U V hu ht),trivial,fun U hU=>?_ ,(Poly.part_cont _).measurable.comp h.borel,fun g U=> congr_arg (fun x:Poly R=> x.part l') (h.gauge g U)⟩
       exact A.K.charged t _ U (fun he=>hU (congr_arg (fun x:Poly R=> x.part l') he))
    refine ⟨fun U V hu hs=> congr_arg (fun x=>v*slice b x) (hF₀.1 U V hu hs),hF₀.2.1,fun U h=>hF₀.2.2.1 _ ?_,fun U=> ?_, ((slice_cont b).measurable.comp hF₀.2.2.2.1).const_mul v,fun u U=>congr_arg (fun x=>v*slice b x) (hF₀.2.2.2.2 u U)⟩
    · intro ht; apply h; change v*slice b (F U)=_; rw [ht]; cases b; exact mul_zero _; exact mul_zero _
    rw [realValue,norm_mul,Real.norm_of_nonneg (Poly.worth hw _).le]; unfold cape; apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le
    apply le_trans (slice_cost ..); rcases i with ⟨i|i,b'⟩
    · exact hE i.val _ _
    exact (hF i.val.1 t U i.val.2).1.trans_eq ((hF i.val.1 t U).norm i.val.2).symm

def leaf (i:J₁)(t:T):Leaf P:= let H₀:= shapes A w hw H g d hE hF i t; ⟨wing A i,realValue A w i t,H₀.1,H₀.2.2.1,H₀.2.1,cape A w g d i.1,H₀.2.2.2.1,H₀.2.2.2.2.2,H₀.2.2.2.2.1⟩
def listCosts (i:J₁): Portrait P T:= ⟨wing A i, cape A w g d i.1,(leaf A w hw H g d hE hF i), fun _=> rfl, fun _=> rfl⟩ -- projection order angle
local notation "ξ"=> listCosts A w hw H g d hE hF
lemma doors (t:T): Encore.doors (brand ξ t) := by
   rintro ⟨i|i,b⟩ ⟨j|j,c⟩ v he he'
   · exact conn_inj A ((Wing.logKey.inj he).trans (Wing.logKey.inj he').symm) |> congr_arg (fun z=> (Sum.inl z.1,z.2))
   · cases he'
   · cases he
   cases he
omit hF hE H hw
include H in
lemma colorCosting (i:J₁) (Q:BudgetPoint): Width.LocalCharge (G:=G) Q (S.ratio.parent ∘ o) (((wing A i).support P).image S.ratio.parent) (fun _=>axis A w i):= by
   refine ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _ q h v hv=>?_⟩
   have he:q=status A i.1:= by contrapose! h; rw [axis,Poly.part_send,if_neg h]
   rw [he] at hv; exact Finset.mem_image_of_mem _ (roots A H i v hv)
omit [Countable I] in
private lemma cover_diffuses {ι:Type} (X_:ι→Support n) (f:ι→ℝ) {B a b} (_hf:∀ i,0 ≤ f i)(h:Hit X_ B f a b): Hit (fun i:ι×Bool=> X_ i.1) B (fun i=> f i.1) a (2*b):= by
    intro x; let g i:= if x∈ X_ i then f i * Real.exp (a*(coverNumber B (X_ i):ℝ)) else 0
    have hT: SumBudget g b:= h x; have he: SumBudget (fun (_:Bool)=> (1:ℝ)) 2:=budget_finite (fun _=>zero_le_one) (by simp)
    show SumBudget (fun i:ι×Bool=> g i.1) (2*b); simpa only [mul_one,mul_comm b] using! budget_prod hT he

lemma parentCost (S:StepData c n) : Extra.Multi.Occupancy (S.ratio.parent) (Fintype.card (Site S.ratio.count)):=by
    -- Proof in RG01/Crest/Path adapted (only here)
    intro j; let Y := Finset.univ.filter fun i=>S.ratio.parent i=j
    change Y.card ≤ _
    have he:Set.InjOn (fun i=>(S.ratio.splitSites i).snd) ↑Y:=by
        intro x hx y hy he; apply S.ratio.splitSites.injective; exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) he
    rw [← Finset.card_image_of_injOn he]; exact Finset.card_le_univ _
set_option quotPrecheck false
variable (B:ℕ)
-- lease.Wands of BOTH estimates or specify E budget at needed read and K separately.
structure Payment {I:Type*}{A':Gallery T I o P R}(w : V→ℝ)(B:ℕ)(a b c' : ℝ)(f:I→ℝ)(d:ℕ→Poly R): Prop where
   bright : Hit A'.E.ground B (fun j=> Poly.toll w (A'.E.mode j) * f j) a b
   positivity i : 0 ≤ f i
   dusk : Hit (fun i=>(P.activities.forced i).support) B (fun i=> Poly.price w (d i)) a c'
-- currencies on exact held witnesses, no jitter from any x,T P.
variable (h:Payment (A':=A) w P.p.B a b c' g d)
include hE hF hw H h
lemma earned (t:T): Lyric.Scale id (fun i=>(brand ξ t i).crest) (brand ξ t) (fun _=>1) (Fintype.card (Site S.ratio.count)) a (2*(b+c')) S:=by
    let Y (i:J):Support n:= i.elim (fun i=>A.E.ground i.val) (fun i=> ((X).forced i.val.1).support); let f:=cape A w g d
    have hN i:(Y i).Nonempty:=by cases i; exact ⟨_,(A.E.address _).anchor⟩; exact ForcedAddress.inventory_ne ((X).forced _) |>.mono ( (X).forced _|>.inventory_sup)
    have he i:0 ≤ f i:=by cases i; exact mul_nonneg (Poly.worth hw _).le (h.positivity _); exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _)
    have hY i : (brand ξ t i).crest=Y i.1:= wingE A H _ _
    have hh(i:J₁): Palette.wages (brand ξ t) (fun _=>1) i=f i.1:= one_mul _
    have hH : Hit Y P.p.B f a (b+c'):= by
       intro x
       have hr: Hit (fun j:ℕ×R.Mode=> ((X).forced j.1).support) (p).B (fun i:ℕ×R.Mode=> Poly.toll w i.2 * ‖(d i.1).part i.2‖) a c':= CoefficientPrices.tallyI («p»:=P.p) _ _ h.dusk (fun i (j:R.Mode)=>Poly.toll w j * ‖(d i).part j‖) (fun i j=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun i=>le_rfl)
       let u i:= if x∈Y i then f i*Real.exp (a*(coverNumber (p).B (Y i):ℝ)) else 0
       have h₁: SumBudget (u ∘ Sum.inl) b:=budget_pull (Subtype.val : Fires A→ I) (show Injective (Subtype.val («p»:=fun i=> ¬ A.E.clear i)) from Subtype.val_injective) (h.bright x)
       have h₂: SumBudget (u ∘ Sum.inr) c':=budget_pull (Subtype.val : Fog0 → ℕ× R.Mode) (show Injective (Subtype.val («p»:=fun i : ℕ×R.Mode=> i.2≠R.quiet ∧ Origins (o:=o) ((P.activities.forced i.1).support) i.2.val)) from Subtype.val_injective) (hr x)
       have he:= HasSum.sum (f:=u) h₁.2.1.hasSum h₂.2.1.hasSum; refine ⟨fun i=>?_,he.summable,he.tsum_eq.trans_le (add_le_add h₁.2.2 h₂.2.2)⟩; cases i; exact h₁.1 _; exact h₂.1 _
    have hL:= cover_diffuses Y f he hH
    refine ⟨fun _=>zero_le_one,fun i _=>?_ , ?_,budget_nonneg (hL 0),parentCost S⟩
    · obtain ⟨x,h⟩:= hN i.1; rw [← hY i] at h; exact ⟨x,h,h⟩
    intro x; simp_rw [hY,hh]; convert hL x using 1; ext i; split <;> ring

omit h hE hF hw
end YM.QuadraticLocal.Trigger
