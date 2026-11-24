import YM.Juniper.Bright.Commit
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
/-!
 # The atlas joining theorem **core local integration**
 from supplies on the Wallet/local compatible arenas (bound soon for pure). Enlarged
 halos admitted BEFORE. Surplus from superpolynomial lags. A regular budget $PAID$ on
 the analytic model can be converted to this epoch to construct new E-moved reclosed density;
 even before knowing if analytic model has right sizes, at any period, this identity. It
 preserves CHORUS (sign orientation for cold-tag Mercury) while creating the high-order
 bound inside SAME pipes with structured control; no assumption of estimate AFTER returning!
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona Match Song Meadow Refrain Slide
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes Marlin Trio
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G}
      {W μ x C s t δ K u v:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k l m b w z:ℕ} {S : StepData c f} {T:Tube G S} {R: Rep G f}
   {I:Cash W x μ L Q o C T R}{B:BudgetPoint}{V : Config G c}
local notation "F"=> plusone I (blank I) χ s
variable {Y₀:Stars→ Side}{a :Site c} (DY:ℕ) {hb:∀ i:Stars,(Y₀ i).val=2*(w+i.val)}{f₀:∀ i:Stars,Trio.Offer G (Y₀ i)} {Y:Shelf I n}
local notation "g"=> living χ I k Y B.B m s
local notation "Z"=> (selection Y k B.B m)
local notation "r"=> leftOver Z s χ
local notation "Φ"=> (Bright.difference (χ:=χ) (s:=s) (B:=B) (m:=m) (k:=k) (Y:=Y) DY hb f₀)
local notation "h₀"=> (posting B I)

lemma lot (H : Collection.Local (Song.posting B I) B F K δ) (h:Shelf.terrace n k ≤ l) (hC:2*radiusB x≤ l) (hB:B.B= radiusB x) (m:ℕ)(Y:Shelf I n):
    ‖earnAll s χ I B (selection Y k B.B m) a V‖ ≤ (ballCost l:ℝ)* K :=by
   -- abstract ANY shelves; adapt anchor-bill lemma Trio.whisk without requiring Destiny reanchored dictionary
   let X:= lantern I (selection Y k B.B m); let U:= neighbors l a
   obtain ⟨p,hp,hp'⟩:= H.cheap
   let f i y:= if ((posting B I).reg i).site=y then p i*Real.exp (preExponent B*coverNumber B.B ((posting B I).reg i).support) else 0
   let t i:= Meadow.garnerAt I B a i; let u i:= (Song.posting B I|>.read F|>.regularOccurrence B i V)
   have hh i (hi:i∈ X) : ‖t i*u i‖ ≤ ∑ j∈U,f i j:=by
      by_cases hv:t i=0; · rw [hv,zero_mul,norm_zero]; exact sum_nonneg fun k _=> (hp' k).1 i
      have hb:= candles_size B hB Y h hC a i hi hv; rw [norm_mul,Real.norm_of_nonneg (show 0≤t i from Meadow.nonnegative ..)]; let y:= ((posting B I).reg i).site
      unfold f; rw [sum_ite_eq,if_pos (hb.2 ((posting B I).reg i).anchor)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (show t i≤1 from Meadow.portions ..)).trans ((CouplingShape.mask_cost (hp i) V).trans (le_mul_of_one_le_right (hp i|>.1) (Real.one_le_exp (show 0≤ preExponent B* _ from mul_nonneg (Song.headline B).exponent_pos.le (Nat.cast_nonneg _)))))
   unfold earnAll; apply (norm_sum_le ..).trans ((sum_le_sum hh).trans _); rw [sum_comm]; refine le_trans (sum_le_sum (fun x _=> (budget_sum (hp' x) X : ∑ i∈ X,f i x≤ K))) ?_
   rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) H.H_nonneg
variable {K₁ w0 u' a' α γ p:ℝ}{Ks:Stars→ℝ}
def breach (B:ℕ)(v:ℝ)(f: Stars→ℝ)(Y:Stars→Side):ℝ:= (ballCost B:ℝ)*v+(ballCost B:ℝ)*v+∑ i:Stars, |Slide.ray i| *((Fintype.card (Site (Y i)):ℝ)*(f i+f i))

-- Atlas income inputs. Keep in true β & κ unit. phy orientation Step. Later ask Spark reclose.
-- retaining d pole at unmasked denominator.
variable (hk : 0<l) (hp:4*l+16 ≤ c.val)(hB:B.B=radiusB x)(hA:Shelf.terrace n k ≤ l)(hC:2*radiusB x ≤ l)(ha:2*l ≤w)(hs: w+4 ≤ DY)(hr:2*DY ≤ b)
-- avoid local notation in declarations
variable (H : Collection.Local (Song.posting B I) B (plusone I (blank I) χ s) K δ)
-- Wm
include H hB hA hC
lemma revenue (V:Config G c) (x:Site c) (hh:flags B.threshold V=∅) (Y:Shelf I n) (m:ℕ):
    ‖living χ I k Y B.B m s x V‖ ≤ (ballCost l:ℝ)*K:= by
   have hk := Bright.lot (a:=x) (V:=V) H hA hC hB m Y; rw [Bright.normal _ _ hh] at hk; rw [Bright.candles B,Finset.sum_apply]; exact hk

include hs
lemma bought (he : ∀ i (V: Config G (Y₀ i)), flags B.threshold V=∅→∀ x, ‖f₀ i x V‖ ≤ Ks i) (a:Site c)(V:Config G c):
     ‖Φ a V‖ ≤ breach l K Ks Y₀ := (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (lot H hA hC hB _ _) (revenue hB hA hC H (1: Config G c) a (UVNext.CouplingReset.flags_one B) Y m))) (Trio.stipends B V hb DY f₀ Ks he hs a))
include hr ha
lemma trimmedCost (he: ∀ i j,B.Regular univ (f₀ i j))(a:Site c): Trio.Tidy B (neighbors b a) (Φ a):= by
   refine Trio.tidy_sub B (u:=earnAll s χ I B Z a - fun V:Config G c=> (g a (1:Config G c))) (v:=Trio.unearned B hb DY (Trio.rip f₀) a) ?_ ?_
   · refine Trio.tidy_sub B (Trio.tidy_sum B _ (lantern I Z) _ fun i hi=> ?_) (Trio.tidy_const ..)
     by_cases hv:Meadow.garnerAt I B a i=0; · simp only [hv,zero_mul]; exact Trio.tidy_const ..
     refine Trio.tidy_scale B _ (Trio.tidy_mask B (X:=((posting B I).reg i).support) (?_ : B.Regular _ _) ?_)
     · exact H.smooth i
     intro j hj; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((candles_size B hB Y hA hC a i hi hv).2 hj)).trans (by omega)
   refine Trio.tidy_sum _ _ _ _ fun i _ => Trio.tidy_scale _ _ (Trio.tidy_sum _ _ _ _ fun j _=> Trio.tidy_mask _ (unit_m B hb DY f₀ he hs (Trio.emerge hb i j a) i j) (Trio.patch hb DY hs i j a hr))

include hk hp
lemma funds (he:∀ i j,B.Regular univ (f₀ i j)) (h:Trio.CompatibleP B l (g) f₀)
    (hh: ∀ i (V: Config G (Y₀ i)), flags B.threshold V=∅→∀ x, ‖f₀ i x V‖ ≤ Ks i) (hΖ : ∃ f:ℕ→ℝ, (∀ i,0≤ f i ∧ ∀ V, ‖(F).hardRead i V‖ ≤ f i) ∧ Ac.Hit (fun i=>((h₀).hard i).support) B.B f (B.supportExponent+1+1) K₁) (hR: Payments.Rates B.B p K₁ u' α)
    (hT:∀ i:Site c,(coverNumber B.B (neighbors b i):ℝ) ≤ a')(hη: Marlin.tithe b (breach l K Ks Y₀) B a'≤ u') (u : Trio.Offer G c) : Ingredients (Marlin.lodge h₀ DY b) (Marlin.dummy (bison r u Φ)) (raiser B) 0 p:=by -- maybe hR order
   obtain ⟨f,hq,hF⟩:= hΖ; refine Marlin.stakes B h₀ DY b r u Φ ⟨H.family.sym,H.family.symtest,H.family.meas,H.family.meas_test,H.family.reads,H.family.reads_test,H.family.permit⟩ (leftover_moves Z H) hR hq hF (trimmedCost DY hB hA hC ha hs hr H he) (fun i U hx he=> hx (Bright.scrub DY hk hp hB hA hC ha hs hr h he)) (Bright.bought DY hB hA hC hs H hh) hT hη
variable (Y) (f₀) (hb)
-- Need outfit:`Moved` computes small rep before computing final projection. Preserve both the budget AND `Work.H02.answer` reserve
omit H hr hp hk ha hC hA hB hs
theorem emerged {ζ p' ℓ:ℝ} (hp:Ingredients (Marlin.lodge h₀ DY b) (Marlin.dummy (bison r (Trio.ornament hb f₀) Φ)) (raiser B) 0 u)
    (he:Collection.Local (posting B I) B F K δ) (hv:Collection.Local (posting B I) B r t δ) (u': Trio.Offer G c) (hq:Meadow.Budget B (Marlin.leap DY) u' ℓ) (hs:Meadow.Budget B (Marlin.leap DY) (Trio.ornament hb f₀-u') p') (hk:∀ V,S.push R.beta R.eval V=earlyValue (posting B I) T.down T.low B F R.beta ζ s V):
    let X:=Marlin.lodge (posting B I) DY b; let g':=Trio.ornament hb f₀; let A₀:= Marlin.bison r g' Φ; let F₀:= Marlin.poursP B X A₀; let Y₁:= Marlin.pluck B X; let L':= ({r with logRead:=fun _=>0}:Collection.Source G c)
    Collection.Local Y₁ B F₀ (t+turnFee B*(p'+ℓ)) u ∧ Meadow.Budget B Y₁.reg (F₀.logRead-(Marlin.bison L' u' Φ|>.regular)) (t+turnFee B*p') ∧ (∀ V,S.push R.beta R.eval V=earlyValue Y₁ T.down T.low B F₀ R.beta (ζ-(g 0 1)) s V):=by
   intro X g' A₀ F₀ Y₁ L'
   obtain ⟨q,h,hx⟩:= hv.cheap; have hw:Meadow.Budget B (posting B I).reg (r).logRead t:=⟨q,hx,fun i=>⟨hv.smooth i,h i⟩⟩
   refine ⟨sous hp (Marlin.reg_bison (posting B I) DY b r g' Φ hw (Bright.splits _ _ _ (Eq.symm (sub_add_cancel g' u')) hs hq)) (fun s b'=> Marlin.reeds (posting B I) DY b r g' Φ s b' (hv.transforms s b').some),?_,fun V=> ?_⟩
   · have ht: F₀.logRead-(bison L' u' Φ|>.regular)=(bison (r) (g'-u') Φ).regular := by
        ext i j; change F₀.logRead i j-( _) = _; unfold F₀ poursP A₀ bison; dsimp only [Function.comp_apply]; cases h:(leanU c i) with
        | inl j=> simp [L'] -- syntax
        | inr i=> change Song.Rim _ * _- Song.Rim _*_ = Song.Rim _ *_; simp only [Pi.sub_apply,Function.comp_apply]; ring
     rw [ht]; exact Marlin.reg_bison (posting B I) DY b r (g'-u') Φ hw hs
   rw [hk]; apply Marlin.carries B (posting B I) DY b r g' Φ V F (fun _=> And.intro rfl rfl) T.down T.low R.beta ζ s _ hp hw (fun V=> Bright.arranged DY hb f₀ he (V:=V)) he.transforms hv.transforms
end YM.Juniper.Bright
