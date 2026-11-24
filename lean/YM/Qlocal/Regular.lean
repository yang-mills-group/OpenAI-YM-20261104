import YM.RGComparison01.Marks.Ropes

/-!
Uniform in arbitrary (e.g. independent tests) payloads. A real estimate IN the
expansion on marked output, from Leaf (may be regular OR forced + mixed Team),
with high-cluster gain, and paid on inherited e occurrences also in these mixed terms.
These are analytic estimates using the Sector machinery for the literal Wilson step,
not formal implications from unmarked output estimates. Note: part only, `Cl` is
just the regular-log terms; see below. The flux/connection to the joint polynomial
is separate.

This uses and extends the `YM/RGComparison01` branch (pay attention to name).
The matching of signatures with different test payloads is similar in spirit to
`Comparison/Remainder/Pilaster`. Some of those branches are not mutually importable.

To pay *relative* perturbations one uses these on marker TYPES (indexed by ι)
having *their own prices*, carried on the outgoing cluster by the full lists
of tickets (`tags` for one input occurrence / cluster of its own markers).
`scale` in a subsequent ledger can be chosen to include the error-factor on
any subset of those types. This file just works prior to reapplying that scale
and pays all derivatives in common layout. Does NOT use smallness of incoming
marked K itself: if calling on such a small K, normalize it TOO, before this bound.
This file also does not identify any analytic approximation to the low-order
all-regular model terms; the low cluster budget is a *rough* budget. (But Heavy
need not be approximated, through retired order.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ : Chi}

-- A single physical layout of real (not complexified-coupling) tails.
-- Note that we never require a different vacuum or a different label space at each test.
variable (M : ι → Leaf R) (D : Ω → ι → Leaf R)

/-- Equal prices almost never mean equal payloads. Take Leaf weights to be
  **common bounds**, like all mask/addresses. Use Ω incl all independent tests. -/
structure Roster : Prop where
  turns (x : Ω) (i : ι) : (D x i).turn = (M i).turn
  money (x : Ω) (i : ι) : (D x i).weight = (M i).weight

namespace Roster
variable {M D} (h : Roster M D)
include h

theorem marks (x : Ω) (S : StepData c f) : Palette.sign (D x) S = Palette.sign M S :=
  funext fun i => congr_arg (fun w : Wing => w.badge S) (h.turns x i)

theorem address (x : Ω) (i : ι) : (D x i).crest = (M i).crest :=
  congr_arg (fun w : Wing => w.support R) (h.turns x i)

def tickets (S : StepData c f) (x : Ω) : Tickets (Palette.sign M S) ≃ Tickets (Palette.sign (D x) S) :=
  { toFun i := ⟨i.val,(h.marks x S).symm ▸ i.prop⟩
    invFun i := ⟨i.val,h.marks x S ▸ i.prop⟩
    left_inv _ := rfl
    right_inv _ := rfl }

local notation "π" => Palette.sign M S
variable (x : Ω)
local notation "Tₓ" => h.tickets S x

lemma val_eq (i : Tickets π) : (Tₓ i).val = i.val := rfl
lemma signs_eq (i : Tickets π) : (Tₓ i).reach = i.reach := by
  change i.val.image (Palette.sign (D x) S) = i.val.image (Palette.sign M S)
  rw [h.marks]
lemma weight_eq (i : Tickets π) : (Palette.team (D x) (Tₓ i)).weight = (Palette.team M i).weight := by
  rw [Palette.worth,Palette.worth,h.val_eq]
  exact prod_congr rfl fun j _=> h.money x j

variable (H)
def castLabel : Cl M H ≃ Cl (D x) H where
  toFun u := ⟨u.1,fun i=> ((u.2 i).1,h.tickets _ x (u.2 i).2)⟩
  invFun u := ⟨u.1,fun i=> ((u.2 i).1,(h.tickets _ x).symm (u.2 i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

local notation "cₓ" => castLabel H h x

theorem geometry (p : Cl M H) : origins (D x) H (cₓ p) = origins M H p := rfl
theorem number (p : Cl M H) : allot (cₓ p)=allot p:= rfl
-- more detailed: preserve every full label & slot as well. Important for filing supports.
lemma tags (p : Cl M H)(i : Option (Fin p.1)) : ((cₓ p).2 i).2.val=(p.2 i).2.val:= rfl
lemma skeleton (p : Cl M H) (i : Option (Fin p.1)): ((cₓ p).2 i).1=(p.2 i).1:=rfl

/-- common majorant in Angular and footprint currency -/
lemma insurance (p : Cl M H) (g : ι → ℝ) (Y : Utopia H j d e b r χ) (B : ℝ) (t : Head S → ℝ) (k ν : ℕ) :
    RegDebt (D x) g (cₓ p) Y k ν B t = RegDebt M g p Y k ν B t := by
  have hp (i : Option (Fin p.1)) : glaze (D x) g Y k B t ((cₓ p).2 i)= glaze M g Y k B t (p.2 i) := by
    unfold glaze whole
    simp_rw [Palette.label]
    dsimp only [castLabel,Equiv.coe_fn_mk]
    simp only [h.weight_eq,h.val_eq,h.signs_eq]
  unfold RegDebt debt clusters
  have hR : coefficient (seam (D x) H) (cₓ p).2=coefficient (seam M H) p.2:=
    Meadow.movement _ _ _ _ (fun i j=> Iff.rfl)
  rw [h.geometry, hR]
  simp_rw [hp]
  rfl

lemma bench {b : ℝ} {g : ι→ℝ} (he : Pledge.Bench M g b) : Pledge.Bench (D x) g b := by
  obtain ⟨o,hA,hG,hP⟩:=he
  unfold Pledge.Bench
  refine ⟨o,fun i=>?_,hG,?_⟩
  · rw [h.address]; exact hA i
  unfold Palette.wages
  simp_rw [h.address, h.money]; exact hP

end Roster

/- Unlike applying sellers with a different ticket per `x`, this places
   the full supremum in the `leftDerivs` price used within Ac.Hit. -/
structure UniformRooted {n : Side} {γ : Type} (U : γ → Support n) (f : Ω → γ → Config G n → ℝ)
    (P : BudgetPoint) (a t : ℝ) : Prop where
  majorize : ∃ b : γ → ℝ,
    (∀ i,0 ≤ b i ∧ ∀ x,
       P.Regular (U i) (f x i) ∧ ∀ j∈U i,P.supBounds j (U i) (f x i) (b i)) ∧
      Ac.Hit U P.B b a t

namespace UniformRooted
variable {n : Side} {γ : Type} {U : γ → Support n} {V : Ω → γ → Config G n → ℝ}
    {p : BudgetPoint}
theorem specializes (h : UniformRooted U V p a d) (x : Ω) : Checks.Rooted U (V x) p a d := by
 obtain ⟨b,hb,ht⟩ := h.majorize
 exact ⟨b,fun i=>⟨(hb i|>.2 x).1,(hb i).1,(hb i|>.2 x).2⟩,ht⟩

lemma relax (h : UniformRooted U V p a d) (hB : d ≤ b) : UniformRooted U V p a b := by
 obtain ⟨v,hv,hK⟩:= h.majorize; exact ⟨v,hv,fun i=>budget_loosen (hK i) hB⟩

lemma at_zero (h : ∀ r:ℝ,0<r→ UniformRooted U V p a r) : UniformRooted U V p a 0:= by
 obtain ⟨d,hd,hD⟩:= (h _ zero_lt_one).majorize
 refine ⟨fun _=>0,fun i=> ⟨le_rfl,fun x=>?_⟩,fun z=>?_⟩
 · refine ⟨(hd i|>.2 x).1,fun j hj=> ?_⟩
   refine ⟨le_rfl,fun z hz l hl hA=>?_⟩
   apply le_of_forall_gt_imp_ge_of_dense; intro u hu
   let v:=Real.exp (a*coverNumber p.B (U i)); have hv:0<v:=Real.exp_pos _
   obtain ⟨k,hk,hK⟩:= (h _ (mul_pos hu hv)).majorize
   refine ((hk i|>.2 x).2 j hj|>.2 z hz l hl hA).trans (le_of_mul_le_mul_right ?_ hv)
   simpa only [hj,if_true] using budget_single (hK j) i
 simp [SumBudget]
end UniformRooted

variable {M D} (h : Roster M D)
include h
-- binder order style: use abbreviations with `(H)` to clarify.
local notation "Δ" => Roster.castLabel H h
local notation "cL" => Cl M H
variable (H) (p : BudgetPoint) (g : ι→ℝ) (A₀ : Cl M H → Prop)

/-- literal same graph contribution after varying the test; do NOT
 collapse two labelled contributions just because they have same origins. -/
noncomputable abbrev entry (χ : Chi) (x : Ω) (z : cL) := Pillow.glass (D x) g χ (Δ x z)
noncomputable abbrev crop (χ : Chi) (x : Ω) (z : cL) := if A₀ z then entry H h g χ x z else 0

-- omit etc
variable (ha:0≤a) (hχ:p.threshold=Pressure.temp β)(hB:p.B=radiusB β)(hp:p.order ≤ j)(hq:p.power ≤ n)
variable {Ξ : Utopia H j e d b r χ} {e' v' v w t A B : ℝ} {k k' : ℕ}
    (Tκ : Knot Ξ v B A t w v' k) {F' : ℕ→ℝ} {Ψ:ℕ→Prop} (hi:Casing R F' Ψ)(he:∀ i,0≤g i)
local notation "pK" => RegDebt M g
local notation "pD" => maskRaise Ξ Ψ F' v
include hp hq hχ hi he Tκ

lemma regularHere (x:Ω) (i:cL):
    Pillow.pottery (D x) g χ (Δ x i) = masked p.threshold (origins M H i) (entry H h g χ x i) ∧
    p.Regular (origins M H i) (entry H h g χ x i) ∧
    ∀ j∈ origins M H i,p.supBounds j (origins M H i) (entry H h g χ x i) (pK i Ξ k n B pD) := by
 have e := Pillow.pride (D x) g Tκ hi he (Δ x i) p hχ hp hq

 rw [h.geometry,h.insurance] at e
 exact e

include hB

theorem uniform_bill (u:Cl M H→ℝ) (hE : Ac.Hit (origins M H) (radiusB β) (fun z:cL=> u z * pK z Ξ k n B pD) a δ) (ht:0< kα)(hg:∀ z,A₀ z→ kα ≤ u z) :
    UniformRooted (origins M H) (crop H h g A₀ χ) p a (δ/kα) := by
   let f (z:cL) := if A₀ z then pK z Ξ k n B pD else 0
   have hf i:0 ≤ f i:= by
       unfold f; split; swap; · rfl
       have H' : 0 ≤ shiftG β*(1+coverNumber (radiusB β) (origins M H i)) := mul_nonneg (by unfold shiftG; positivity) (add_nonneg zero_le_one (by positivity))
       exact mul_nonneg (pow_nonneg H' _) (Baked.grain M g Ξ i Tκ.paidB hi Tκ.paidE he)
   refine ⟨f,fun i=>⟨hf i,fun x=>?_⟩,fun i=>?_⟩
   · by_cases hX:A₀ i
     · simp only [crop,f,if_pos hX]; exact (regularHere H h p g hχ hp hq Tκ hi he x i).2
     simp only [crop,f,if_neg hX]; exact ⟨CouplingShape.reg_const _,fun _ _=> sup_le (CouplingShape.sup_const _) abs_zero.le⟩
   rw [div_eq_mul_inv,mul_comm δ,hB]; have he':= budget_scale (inv_pos.mpr ht|>.le) (hE i)
   refine budget_mono he' (fun j=>?_) (fun j=>?_)
   · split; · exact mul_nonneg (hf _) (Real.exp_nonneg _)
     exact le_rfl
   split
   next hz=>
     by_cases hh:A₀ j; swap; · unfold f; rw [if_neg hh,zero_mul]; simpa only [hz,if_true] using (he'.1 j)
     unfold f; rw [if_pos hh]; dsimp only; rw [le_inv_mul_iff₀ ht, ← mul_assoc]
     have hy : f j=pK j Ξ k n B pD:= if_pos hh
     exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hg j hh) ((hy) ▸ hf j)) (Real.exp_nonneg _)
   rw [mul_zero]


variable [Fintype ι] {v₀ g₀ h₀ s₀ u₀: ℝ→ℝ}
    (hQ : Cellar Q χ W L S.patch o p.order k k' p.power μ a δ v₀ g₀ h₀ s₀ u₀ β)
    (hs : Pledge.Bench M g (v₀ β))
    (hX : Stamp T)
omit hp hq hi he Tκ
include hχ hB hQ hs hX

/-- Version with the common sup already UNDER the site-hit sum, on
    `Baked.Cl` regular log labels in the primitive step on a Cash.

    Last branch takes one occurrence from the stated inherited E sub-family
    (by `Season.Ode`: undecorated by the mark slot on THAT occurrence). Can
    be mixed with arbitrary marked inputs in here, price is still multiplied by
    the old error factor `e`. The second branch takes the exceptional/retiring
    part *without* any such old E. That is paid from the high-order Taylor
    budget even on these marked branches.
    All powers of g from undoing normalization of marker inputs are separate.
    Compare to `RGComparison01.Pledge.Checks.sellers`, which treats one fixed payload. -/
theorem uniform_retirement (hF : (Tithe.portion R.activities Ψ).EBound R.p e)
    (hFe : e ≤ incomingE G L β) (hw : Height.grow G L β^k ≤ Real.exp (Q.mark L μ β)) :
    (∀ (x:Ω) i,Pillow.pottery (D x) g χ (Δ x i)=masked p.threshold (origins M H i) (entry H h g χ x i)) ∧
    UniformRooted (origins M H) (entry H h g χ) p a (h₀ β) ∧
    UniformRooted (origins M H) (crop H h g (fun z=> Season.Heavy k' z ∧ ¬Season.Ode Ψ z) χ) p a (h₀ β/(Height.grow G L β^k)) ∧
    UniformRooted (origins M H) (crop H h g (Season.Ode Ψ) χ) p a (s₀ β * e) := by
   obtain ⟨j',r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,X,hS,hN⟩:= ((hQ.buys c f S T rfl hX R C H).2)
   have ht': e≤ v₀ β:= hFe.trans (hQ.covers.trans (min_le_right ..))
   have hgt: ∀ i:ι,0≤ g i:= Exists.elim hs fun _ hx=> hx.2.1
   obtain ⟨v,hv,he⟩:= hN _ M g hs Ψ e 1 hF hFe le_rfl (by simpa using ht')
   let d:= Height.grow G L β; have hd:1 ≤ d:= hQ.life
   refine ⟨fun x i=>?_, ?_, ?_,?_⟩
   · exact (regularHere H h p g hχ le_rfl le_rfl hS hv hgt x i).1 
   · have hh:= uniform_bill H h p g (fun _ => True) hχ hB le_rfl le_rfl hS hv hgt _ he zero_lt_one (fun z _=> Season.safe le_rfl hQ.pole (one_le_pow₀ hQ.life) z)
     have hx : entry H h g χ = crop H h g (fun _=>True) χ := by
       funext x i; exact (if_pos True.intro).symm
     rw [hx]; simpa only [div_one] using hh
   · exact uniform_bill H h p g _ hχ hB le_rfl le_rfl hS hv hgt _ he (show 0<d^k from pow_pos (zero_lt_one.trans_le hd) k) (fun z h=> Season.wealth le_rfl hQ.pole (one_le_pow₀ hd) h.1 h.2 hQ.sizes le_rfl hw hQ.long)
   rcases eq_or_lt_of_le (show 0 ≤ e from by obtain ⟨v,h,hB⟩:=hF; exact budget_nonneg (hB 0)) with h0|h0
   · rw [← h0,mul_zero]; apply UniformRooted.at_zero; intro x hx
     have hl : ∀ᶠ y:ℝ in atTop, h₀ β / y ≤ x:= by
         have hl:= tendsto_const_nhds (x:=h₀ β)|>.mul (tendsto_inv_atTop_zero (𝕜:=ℝ)); simp_rw [mul_zero,← div_eq_mul_inv] at hl; exact (hl.eventually (gt_mem_nhds hx)).mono fun _ hx=>hx.le
     obtain ⟨w,hw,hV⟩:= (hl.and (eventually_ge_atTop 1)).exists
     obtain ⟨X,hx,hU⟩:= hN _ M g hs Ψ e w hF hFe hV (by rw [←h0,mul_zero]; exact hQ.crucial.le)
     exact (uniform_bill H h p g _ hχ hB le_rfl le_rfl hS hx hgt _ hU (zero_lt_one.trans_le hV) (fun p h=> Season.oasis hV hQ.pole (one_le_pow₀ hd) h)).relax hw
   let x:=v₀ β/e; have hx:1≤x:= (one_le_div h0).2 ht'
   obtain ⟨X,hX,hU⟩:= hN _ M g hs Ψ e x hF hFe hx (div_mul_cancel₀ _ h0.ne'|>.le)
   apply (uniform_bill H h p g _ hχ hB le_rfl le_rfl hS hX hgt _ hU (zero_lt_one.trans_le hx) (fun p h=> Season.oasis hx hQ.pole (one_le_pow₀ hd) h)).relax
   rw [← hQ.spelled]; apply le_of_eq; unfold x; rw [← div_eq_mul_inv, div_div_eq_mul_div]; ring

end YM.Qlocal
