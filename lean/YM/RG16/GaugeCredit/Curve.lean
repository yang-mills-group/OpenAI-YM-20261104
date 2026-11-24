import YM.RG16.GaugeCredit.Lambda

/-!
# Use origin on SAME representation. Graph comparison from high-order FG budgets.

Sign convention of `Inked`: true transmission **of the model**, minus its predicted model output. Numerically the rendered
forward matrix is IN THRESHOLD coordinates (t based); next files convert a
formal statement in g. Stable estimate only pays the Nullity residual at the
level; connectivity/forced budgets of changing a Rep would not commute with
this telescope. Bind these local hypotheses on input to the very SAME data.

Do not spend the formal model graph-size
estimates in generating a different output graph rep: compose the direction
whose inverse solve uses the *candidate* forward, then expose true equality of
full densities & negligible page prices. Perturbation theory (equality and
very coarse true inverse needed) suffices to bound THAT inverse in every
step. No stack multiplying post-L heroics on the singleton. The real `Gate`
is proved in budget space, not on arbitrary numerical functions. This gives
the differences per vector/unit; not a consistent prescription of
singletons INSIDE a polynomial for mixed coefficients. Rep existence in
larger marker sets still has to be certified for every such operation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Set Function Filter MeasureTheory Lattice Wilson Source RG OPE Labels
open Extra.Histories Relay Bid Cells MergeProof Ribbons Pert
open Trace.Physical Trace.Physical.GermGraph Literal Work.G08 Next.Foundations
open PhysicalNext.Repeat.Legato.Bandage YM.Push.Local ProjectorNext.Equivariance
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}(C:Family G)(H:C.Makes)(N p d:ℕ)
set_option quotPrecheck false
local notation "Λ" => Lambda C.path.levels
local notation "L" => factor C
local notation "P" => C.path.levels
local notation "E" => value (C:=C) d N p
local notation "X!" => measuring C d N p
local notation "μ" => coin C
local notation "σ" => C.label d
local notation "M!" => C.factory d N p
local notation "Y₀" => calValues (C:=C) d N p
local notation "V" => mCost C d N p
local notation "s" => (C.labels.level d).coeffSize
local notation "τ" => transition (C:=C) d N p

abbrev Mat := (C.label d) →ₗ[ℂ] (C.label d)
abbrev Chart := ∀ i:ℕ,(C.label d) → Config G (C.side i p) → ℂ

/-- From heading normalization. Full possible representations of SAME graph
with the fixed top cylinder; `x` is in maker frame, horizon d; θ not
recharged per step here. -/
def Grown (i:ℕ)(D:ℝ)(Y:Chart C p d) : Prop :=
   ∀ x:C.label d, Nullity C N p d i (calValues (C:=C) d N p i x - Y i (measuring C d N p i x))
       (D*mCost C d N p i x)

/-- Model ordinary conditional graph defect. Needs alignment on this concrete
actual Rep; if calculated on another vacuum with same eval, even labels/subsets
that seem to match wouldn't give this. Per-threshold-vector log AND source
costs, germs and full-density equality. Including units. -/
def Inked (i:ℕ)(Y:Chart C p d)(M: Mat C d)(D:ℝ) : Prop :=
    (∀ x,accepted C N p d i (Y i x) x) ∧
       ∀ x:C.label d, Foreground C d N p i (τ i (Y (i+1) x)-Y i (M x)) (D*s x)

lemma mat_cap {k:Mat C d}{r:ℝ}(_hr:0<r)(hz:∀ x:C.label d, s x ≤ r*s (k x)) :
    Bijective k := by
   have hk : Injective k:= by
     apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr (fun u hu=>?_)
     have he:= hz u
     rw [hu,show s 0 = 0 from by simp [Frame.coeffSize],mul_zero] at he
     exact norm_le_zero_iff.mp ((norm_le_size ..).trans he)
   exact ⟨hk, LinearMap.injective_iff_surjective.mp hk⟩

variable {i:ℕ} {u t:ℕ} {M:Mat C d} {Y:Chart C p d} {γ r b:ℝ}
local notation "a" => (factor C i^γ)
local notation "q!" => (factor C i^(-rate))
include H in
lemma held (hN:i<N)(h:Opened C d i p)(hg:Opened C d (i+1) p)(he:Gate C d N p i γ 1)
     (hY:Grown C N p d (i+1) r Y)(hz:Inked C N p d i Y M b) (x:C.label d) :
     ∃ y:C.label d, X! i y=M (X! (i+1) x) ∧
       Nullity C N p d i (calValues d N p i y - Y i (M (X! (i+1) x))) ((b+factor C i^(-rate)*r)* (V (i+1) x)) ∧
       s (X! i x-M (X! (i+1) x)) ≤ (b+factor C i^(-rate)*r) * V (i+1) x := by
    let k:= X! (i+1) x; let w:= M k; let f := Y (i+1) k; let o:=τ i f - Y i w
    let g:= Y₀ (i+1) x-f
    have hq := hY x
    obtain ⟨e,hE,hP⟩:= foreground_splits (hz.2 k) H h hN.le
    obtain ⟨v,hv,hQ⟩:= nullity_toss g he hq
    have ht:= hq.message H hg.post hN
    have hf : Integrable f (prior G _):= by
       have hr: Integrable (Y₀ (i+1) x) (prior G _):= (Ink.invest H hg hN x).message H hg.post hN
       rw [show f = Y₀ (i+1) x - g from (sub_sub_self ..).symm]; exact hr.sub ht
    have hrep:= Nullity.combine hP hQ H h.post hN.le
    let r' := τ i f-Y i w-Y₀ i e + (τ i g-Y₀ i v)
    change Nullity C N p d i r' _ at hrep
    let y:= e+v
    have hx : Y₀ i x= (r'+Y i w)+Y₀ i y:= by
       unfold r' y;rw [cal_add d N p i H h.post hN.le]
       calc
          _= τ i (Y₀ (i+1) x) := factory_eq d N p i H h.post hN x
          _= τ i g + τ i f :=by rw [←transition_add d N p ht hf, sub_add_cancel] -- may need unfold g
          _= _:= by abel
    have hacc := accept_cal H h hN.le x; rw [hx] at hacc
    have hpay := hacc.min ((accepted.combine (Ink.pred hrep) (hz.1 w) H h hN.le).combine (accept_cal H h hN.le y) H h hN.le) H h hN.le
    rw [zero_add] at hpay
    have hp' := (Ink.invest H h hN.le x).pred -- no use
    have hρ : s (X! i x-w) ≤ (b+q!*r)*V (i+1) x:= calc
       _ = s (X! i e+ X! i v):= by rw [hpay,add_sub_cancel_left]; unfold y; rw [measuring_add _ _ _ _ H h hN.le]; -- actually add_sub_cancel_left
       _ ≤ _:= le_trans (Size.add ..) ((add_le_add hE hv).trans_eq (by unfold mCost; rw [add_mul,mul_assoc]))
    refine ⟨x-y,?_ ,?_,hρ⟩
    · rw [measuring_sub _ _ _ _ H h hN.le, hpay,add_sub_cancel_right]
    have hX : Y₀ i (x-y) - Y i w = r':= by
       have hy := cal_add d N p i H h.post hN.le (x-y) y
       rw [sub_add_cancel,hx] at hy; exact sub_eq_of_eq_add (add_right_cancel hy.symm) -- cancellation
    refine (show Nullity C N p d i (Y₀ i (x-y)-Y i w) _ from ?_)
    rw [hX]; convert hrep using 1; change (b+q!*r)*V (i+1) x=b*V (i+1) x+q!*(r*V (i+1) x); ring

include H in
lemma grow_step {D:ℝ}(hr:0≤r)(hb:0≤b)(hN:i<N)(h:Opened C d i p)(hg:Opened C d (i+1) p)(he:Gate C d N p i γ 1)
    (hY:Grown C N p d (i+1) r Y)(hz:Inked C N p d i Y M b)
    (hW: 2* (factor C i^γ)*(b+factor C i^(-rate)*r) ≤ min D 1):
    Grown C N p d i D Y:= by
    have hl:=factor_positive C i
    have hv : 0<a:= Real.rpow_pos_of_pos (zero_lt_one.trans hl) _
    let T (x:C.label d):= M (X! (i+1) x)
    have ht(x) : V (i+1) x ≤ 2*a*s (T x) := by
       have he' := (held C H N p d hN h hg he hY hz x).choose_spec.2.2
       have ha : V i x ≤ s (T x)+(b+q!*r)*V (i+1) x :=
         (show V i x ≤ s (T x)+s (X! i x-T x) from by simpa only [add_sub_cancel] using Size.add _ (T x) (X! i x-T x)).trans (add_le_add (le_refl _) he')
       have hx := he.1 x |>.trans (mul_le_mul_of_nonneg_left ha hv.le)
       have hz := mul_le_mul_of_nonneg_right (hW.trans (min_le_right ..)) (show 0≤V (i+1) x from size_nonneg ..)
       change V (i+1) x ≤ a*(s (T x)+(b+q!*r)*V (i+1) x) at hx
       linarith only [hx,hz]
    have hM : Surjective M := (mat_cap C d (r:=2*a) ?_ ?_).2
    · intro x
      obtain ⟨v,hv'⟩:= hM (X! i x); let z:= (fitting d N p (i+1) H hg hN).symm v
      have hzp:X! (i+1) z=v:=(fitting d N p (i+1) H hg hN).apply_symm_apply v
      have hT:T z=X! i x:= (congr_arg (fun i=> M i) hzp).trans hv' -- subst moves? hv' in T uses z
      obtain ⟨y,hp,hy,-⟩:= held C H N p d hN h hg he hY hz z
      have hp:x=y:= (fitting d N p i H h hN.le).injective (show X! i x=X! i y from hT.symm.trans hp.symm)
      rw [show M (X! (i+1) z) = _ from hT,←hp] at hy -- T abbreviation?
      have hs:0≤b+q!*r:=add_nonneg hb (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hl).le _) hr)
      apply hy.inc; refine (mul_le_mul_of_nonneg_left (ht z) hs).trans ?_
      have hy' := mul_le_mul_of_nonneg_right (hW.trans (min_le_left ..)) (show 0≤ V i x from size_nonneg ..)
      rw [hT]; change (b+q!*r)*(2*a*V i x) ≤ D*V i x; linarith only [hy']
    · exact mul_pos zero_lt_two hv
    intro x; let z:= (fitting d N p (i+1) H hg hN).symm x
    have hT:= ht z; change s (X! (i+1) z) ≤ 2*a*s (M (X! (i+1) z)) at hT; rw [(show X! (i+1) z=x from (fitting d N p (i+1) H hg hN).apply_symm_apply ..)] at hT; exact hT

variable (K:Ribbons.Materials C) (hpace: ∀ i,((C.S.block i).val:ℝ) ≤ Real.log (Lambda C.path.levels i))
section
include hpace K
/-- Fixed-loss budget. `x` is the negotiated comparison WITH loss (e.g. r+1−2η), `y` is the **better** loss from local input. Gate specialized to ε=1. buys every sufficiently fine m, AND N and period independent. No more loss per persistent step. -/
theorem hat_budget {x y:ℝ}(hx:0<x)(hxy:x<y){γ:ℝ}(hγ:0<γ)(hr:γ<rate) :
      ∀ᶠ t:ℕ in atTop,∀ i≥t,∀ p N,i<N →
          (Opened C d i p ∧ Opened C d (i+1) p ∧ Gate C d N p i γ 1) ∧
          2*L i^γ*(coin C y i+ L i^(-rate)*coin C x (i+1)) ≤ min (coin C x i) 1 := by
    have hp : RateLE atTop Λ (fun i=> 4*(L i^γ)) 0:= by
       simpa only [zero_add,mul_zero] using! (RateLE.const 4 (lambda_leads C K.hG)).mul (((platelet C K.hG hpace).rpow γ).pays (lambda_leads C K.hG))
    obtain ⟨n,hn⟩:=eventually_atTop.mp ((quarter C hr).and (spend C K.hG hxy hp))
    filter_upwards [message_graph C d K hγ (zero_lt_one),eventually_ge_atTop n] with t he h i hi p N hN
    obtain ⟨h₁,h₂⟩ := he i hi p N hN; refine ⟨⟨h₁.1,h₁.2,h₂⟩,?_⟩
    rw [min_eq_left (smaller_receipt C hx.le i)]
    have hD: (coin C x (i+1)) ≤ coin C x i:= coin_down C K.hG hx.le (Nat.le_succ _)
    have hn:= hn i (h.trans hi); have hy : 4*L i^γ*coin C y i ≤ coin C x i:= hn.2
    have hT:= mul_le_mul hn.1 hD (coin_pos C x (i+1)).le (by norm_num)
    have hv:= coin_pos C x i
    linarith only [hT,hy,hv]

/-- Actual transfer comparison on THIS spelling of the Wilson history. At all
reports of tail. Also for N=t; here `P k can encode, not a regulator limit`.
No Gram (beyond invertibility of indicated single graph step, prepaid by H)
needed. All threshold coordinates at indicated step on this Rep. -/
theorem recolor {x y:ℝ}(hx:0<x) (hxy:x<y) : ∀ᶠ t:ℕ in atTop,
    ∀ N p:ℕ,t ≤ N → ∀ M : ℕ→Mat C d,∀ Y:Chart C p d,
       Grown C N p d N (coin C y N) Y → (∀ i ≥ t, i<N → Inked C N p d i Y (M i) (coin C y i)) →
        (∀ i≥t,i≤N→ Grown C N p d i (coin C x i) Y) ∧
           (∀ i≥t,i<N→ ∀ w:C.label d, s (measuring C d N p i w- M i (measuring C d N p (i+1) w)) ≤
                coin C x i*mCost C d N p (i+1) w):= by
      have hr : 0 < rate:= by unfold rate; norm_num
      filter_upwards [hat_budget C d K hpace hx hxy (γ:=rate/2) (half_pos hr) (half_lt_self hr)] with i h N p hi M Y hV hY
      have he (v) (h0:i≤v)(ht:v≤N) : Grown C N p d v (coin C x v) Y := by
         induction ht using Nat.decreasingInduction with
         | self=> exact fun w=> Ink.inc (hV w) (mul_le_mul_of_nonneg_right (coin_weaken C hxy.le _) (size_nonneg ..))
         | of_succ j hj ih=>
           have hp:=h j h0 p N hj
           exact grow_step C K.makes N p d (coin_pos C x (j+1)).le (coin_pos C y j).le hj hp.1.1 hp.1.2.1 hp.1.2.2 (ih (h0.trans j.le_succ)) (hY j h0 hj) hp.2
      refine ⟨he,fun j hj hN w=>?_⟩
      have ht:= h j hj p N hN
      have hb:=(held C K.makes N p d hN ht.1.1 ht.1.2.1 ht.1.2.2 (he (j+1) (hj.trans j.le_succ) hN) (hY j hj hN) w).choose_spec.2.2
      apply le_trans hb; refine mul_le_mul_of_nonneg_right ?_ (size_nonneg ..)
      have hl:=factor_positive C j
      have hx : 1 ≤ 2*L j^(rate/2):=one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_rpow hl.le (half_pos hr).le)
      have hy : 0≤μ y j+L j ^(-rate) *μ x (j+1):= add_nonneg (coin_pos C y j).le (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hl).le _) (coin_pos ..).le)
      exact (le_mul_of_one_le_left hy hx).trans (ht.2.trans (min_le_left ..))
end
end YM.RG16.Guarding
