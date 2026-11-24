import YM.RG01.Vacuum.Exceptions
import YM.UVExtension.Oasis.Flora
import YM.Pert.Asymptotics.RawAxis

/-!
# Actual analytic sub-estimate — reduction to the low-arity, zero-share log
primitives

Exhibit on the fixed construction, no change of family, schedule or hard
partners, certifying the reduction with the existing quantitative purchases
only. Pointwise push identity retaining α and extensive scalar through
that split; arbitrary fixed output-order budget and admissible eta, before
canonical reclosure. This discharges subpieces of the *vacuum* clause,
not the analytic grading or E contraction on the residual primitive list,
nor any marked insertion conclusion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe UVExtension Spire Orchard Mast Oasis
open Real

variable {G:Gauge} {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{R:Factor A} {hG : G.Simple} (S : Uses R hG)

/-- Inspectable purchase on the exact component dictionary, before projection.
In (Decision ...) the O parameter tracks the same vacuum scalar. Constraint on
surviving letters is on the assigned imported `degree`, `overlap` and `depth`, NOT
all statements that might use a notation `grade`, `seed` or `length`. -/
def delivered (N m n : ℕ) (H : Guide A.B R.shape N m n (S.realBeat 0 N n (m+1))) : Prop :=
  Opera.Price A.B R.shape N m n _ H

abbrev cost (c g : ℝ) (d:ℕ)(η:ℝ):=
  c*(Real.sqrt 2)^η*g^((d+1:ℕ)-η)

private def realg (m n N) := (Real.sqrt (S.realBeat 0 N n m).beta)⁻¹

section issuance
variable {N m n:ℕ} (hm:m<N)
include hm
lemma hasGuide : ∃ H : Guide A.B R.shape N m n (S.realBeat 0 N n (m+1)), delivered S N m n H := by
  obtain ⟨hv,hb⟩ := (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
  exact Opera.feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income hv hb

omit hm
/-- Constants uniform in every period, forest, cutoff N and level m. Hard
pre-move budget with its constructor additional support exponent is bounded
even *after one forced divisor*, also times k powers of hatBeta (finer).
The hard address functions and their payloads are common between the two
Local budgets; per argument `U` their unscaled costs already cover bad and
failed-mask regions, and UsesFinal/supports keep the tests. -/
lemma cleared (k d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (m n N : ℕ), m<N →
      ∀ H : Guide A.B R.shape N m n (S.realBeat 0 N n (m+1)), delivered S N m n H →
      ∀ O : Return.Wood A.B m n,
      let b:=(S.realBeat 0 N n (m+1)).beta
      let w := A.B.a.clock.forcedAllowance m
      0 < realg S (m+1) n N ∧ realg S (m+1) n N ≤ Real.sqrt 2 ∧
      (∀ η : ℝ,0 ≤ η→ Decision R H O (importedTail R H (d+1)) (Opera.earlyFee (p:=R.expense) A.B N m b) (cost c (realg S (m+1) n N) d η) w ∧
        A.B.a.clock.hatBeta (m+1)^k * (w/Real.sqrt w) ≤ cost c (realg S (m+1) n N) d η) := by
  obtain ⟨c,hc,h⟩:= markCurrency R hG (d+1)
  obtain ⟨a,ha,hA⟩:= Flat.currency A.B.a hG (d+1) k
  let z:= Real.sqrt 2; have hz:0<z:=by unfold z; positivity
  let t := z^(d+1)+c+a
  have hT:0<t:=by unfold t; positivity
  refine ⟨t,hT.le,?_⟩
  intro m n N hi H hH O b w
  let Y:=S.realBeat 0 N n (m+1)
  let g:=realg S (m+1) n N
  obtain ⟨hv,hb⟩ := (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hi
  have hy:1 < A.B.a.clock.hatBeta (m+1):= A.B.a.fits.delayed _
  have hB : 0 < b:=lt_of_lt_of_le (half_pos (zero_lt_one.trans hy)) hb.1
  have hg:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr hB)
  have hp:g ≤ z:=by
    change (Real.sqrt b)⁻¹ ≤ _; rw [inv_le_comm₀ (Real.sqrt_pos.mpr hB) hz]
    unfold z; rw [← Real.sqrt_inv]; apply Real.sqrt_le_sqrt; linarith only [hb.1,hy]
  refine ⟨hg,hp,?_⟩; intro η hη
  have hx := admission (d+1) η hη hg hp
  have hD : Decision R H O (importedTail R H (d+1)) (Opera.earlyFee (p:=R.expense) A.B N m b)
      ((z^(d+1)+c)*g^(d+1)) w := rare R H O hH hi hv hb _ (h m N hi b hb)
  have he {u:ℝ} (hu:u≤t):u*g^(d+1) ≤ cost t g d η:=by
    unfold cost; rw [mul_assoc,mul_comm _ (g^(_-η))]
    exact mul_le_mul hu hx (pow_nonneg hg.le _) hT.le
  constructor
  · unfold Decision at hD ⊢; dsimp only at hD ⊢; refine ⟨hD.1,?_ ,hD.2.2⟩
    obtain ⟨hF,hK,hM,⟨i,hi,hI⟩,hS⟩:=hD.2.1
    exact ⟨hF,hK,hM,⟨i,hi,fun x=> Extra.Iteration.Cost.enlarge (hI x) (he (le_add_of_nonneg_right ha))⟩,hS⟩
  have hd:0<w:=Real.exp_pos _
  have hs:w/Real.sqrt w=Real.sqrt w:=(div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hd))).mpr (Real.mul_self_sqrt hd.le).symm
  rw [hs]
  exact (hA m b hB (Or.inl hb.2)).trans (he (le_add_of_nonneg_left (by positivity)))


end issuance
-- public certification binds only retained data relevant here, naming exactly
-- the H determined and tag roots protected by R.brand. Universally quantified
-- Step without requiring access to private choice proofs.
structure OnUsed (k d : ℕ) (c : ℝ) : Prop where
    selects (m n N : ℕ)(hi:m<N): ∃ H : Guide A.B R.shape N m n (S.realBeat 0 N n (m+1)), delivered S N m n H
    answers (m n N : ℕ)(hi:m<N)
      {w:Bid.Worth} {t:ℕ→ℕ}{K:ℕ→ℝ}{Q:Bandage R K w}(L:Cellar S t Q)
      -- literal Real beta law at active calendar: any cylinder choices
      (C: Family G)(hC : C=Cellar.yard (roseA S) L) (O:Return.Wood A.B m n):
      let f := Pert.Asymptotics.regulatorRun C N n (m+1)
      C.beta N n=(S.realBeat 0 N n N).beta ∧ C.path.β N n (m+1)=(S.realBeat 0 N n (m+1)).beta ∧
      0 < f ∧ f ≤ Real.sqrt 2 ∧
      let a := A.B.a.clock.forcedAllowance m
      ∀ H : Guide A.B R.shape N m n (S.realBeat 0 N n (m+1)), delivered S N m n H →
        ∀ η : ℝ,0 ≤ η → Decision R H O (importedTail R H (d+1)) (Opera.earlyFee (p:=R.expense) A.B N m (C.path.β N n (m+1))) (cost c f d η) a ∧
        A.B.a.clock.hatBeta (m+1)^k * (a/Real.sqrt a) ≤ cost c f d η
-- use .selects inhabitance to get pos without additional premises
lemma sameCurrency (k d : ℕ) : ∃ c : ℝ,0 ≤ c ∧ OnUsed S k d c := by
    obtain ⟨c,hc,h⟩:=cleared S k d
    refine ⟨c,hc,fun m n N hi=> hasGuide S hi,?_⟩
    intro m n N hi w t K Q L C hC O; subst C; intro f
    obtain ⟨H,hH⟩:= hasGuide S (n:=n) hi
    obtain ⟨he,hf,hZ⟩:=h m n N hi H hH O
    exact ⟨rfl,rfl,he,hf,fun i ht=> (h m n N hi i ht O).2.2⟩

variable {G : Gauge} {C : YM.Family G} {hG:G.Simple}

/-- Producer instance on any of the pinned UV physical constructions. Keep
all witness choices visibly tied by the same erection equality. In particular
the representation identity in Decision reads the literally same
pre-normalization push by that equality. -/
theorem onFloral (h : Oasis.Floral (hG:=hG) C) :
    ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(R:Factor A)(S:Uses R hG)
       (K:ℕ→ℝ)(w:Bid.Worth)(Q:Bandage R K w)(t:ℕ→ℕ)(L:Cellar S t Q),
       C=Cellar.yard (roseA S) L ∧
       ∀ k d : ℕ,∃ c : ℝ, 0 ≤ c ∧ OnUsed S k d c := by
    obtain ⟨M,P,A,R,S,V,t,K,w,Q,L,h₀,h₁,-⟩:= h
    exact ⟨M,P,A,R,S,K,w,Q,t,L,h₁,sameCurrency S⟩

-- adapters to bare comparison on law (coarse evaluation)
theorem useActualTransfer (k d : ℕ) {c : ℝ} (h : OnUsed S k d c)
    {N n m : ℕ}(hm:m<N){w:Bid.Worth}{t:ℕ→ℕ}{K:ℕ→ℝ}{Q:Bandage R K w}(L:Cellar S t Q)(hC:(Cellar.yard (roseA S) L).Makes) (O:Return.Wood A.B m n) (η : ℝ) (he:0≤η):
    let C':= Cellar.yard (roseA S) L
    ∀ H : Guide A.B R.shape N m n (C'.path.rep N n (m+1)), Opera.Price A.B R.shape N m n _ H →
      let A₀:= C'.path.rep N n m
      let B₀:= C'.path.rep N n (m+1)
      let p':=C'.path.levels.budget m
      let Z:=Song.posting p' H
      -- even with all indicators on; no filtering by old coarse mask used in this identity
      -- uses canonical C' data via defeq in the two shelf arguments
      let D:H.fragrances→ Prop:=importedTail R (u:=B₀) H (d+1)
      let u:= shelf R (u:=B₀) H D false
      let v:= shelf R (u:=B₀) H D true
      let x:= Pert.Asymptotics.regulatorRun C' N n (m+1)
      A₀.eval = earlyValue Z (A.B.kin.path N m) ((A.B.a.params m).clip) p' u B₀.beta (weighty H Chi.canonical O) (Alpha (A:=A) N m) * exponentialShare Z p' v ∧
        (Z.read v).EBound p' (cost c x d η) ∧ (Z.read u).KBound p' (C'.path.levels.clock.forcedAllowance m) := by
  intro C' H hj a b p Z D U V x
  have ht:=h.answers m n N hm L _ rfl O |>.2.2.2.2 H hj η he|>.1
  unfold Decision at ht; dsimp only at ht
  have hv := ht.2.2
  refine ⟨(hC.wilson.steps N n m hm).1.trans hv,ht.2.1.unweighted, localK ht.1⟩

end YM.RG01.Vacuum
