import YM.RG01.Vacuum.Family
import YM.RG01.Vacuum.Exchange
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-!
# Bill at the committed actual RG step

The caller need not synthesize new stronger scheduling assumptions or a new
complex coupling trajectory. Use the two tree estimates literally at the
Factor pledge, without asking for smaller E or extra support widths. Exhibit
one catalogue representing the exact pushed vacuum (pre alignment/reset),
with (i) the keep still at the early provision costs (includes the substrate
and kinetic alpha, NOT at the small difference cost), (ii) hard occurrence &
eligibility on the SAME listing, (iii) regular residual for a high-arity cut
K with the perturbative comparison rate, support and derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {m n N : ℕ}
local notation "Z"=> A.B.a
-- define Bundle types serving F,k consumer. Guide drives H,J=I. path `ships`. indexing build
abbrev Alpha (N m) := A.B.kin.alpha N m
abbrev Anchor (N m n) := Pressure.Testing.ships A.B N m n
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)}
   (H : Guide A.B R.shape N m n u) (hH : Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : Lives A.B.bake N (m+1) n u) (hb : u.beta ∈ band A.B.a (m+1))

/-- One **full** pre-reset re-expression and its exact log correction.
See Deadlines for Rate: the hard amount here will be bounded by the
construction's `forecastK` (itself ≤ forcedAllowance m). Does not assert
anything on the high-order *low* log Taylor errors or unrelated alignment fees.
-/
def Prealigned (M : ℕ) (O : Return.Wood A.B m n) (H : Guide A.B R.shape N m n u) (e t w : ℝ) : Prop :=
    let p:=A.B.a.budget m
    let S:=A.B.a.clock.op m n
    let W:= A.B.kin.path N m
    let ι : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
    let γ := Alpha (A:=A) N m
    let keep := weigh H ι Chi.canonical (arityKeep M) true γ
    let err := weigh H ι Chi.canonical (arityFilter M) false γ
    let A' := posting p H
    Collection.Local A' p keep e w ∧ Collection.Local A' p err t w ∧
      S.push u.beta u.eval = earlyValue A' W ((A.B.a.params m).clip) p keep u.beta
        (weighty H Chi.canonical O) γ * exponentialShare A' p err

private lemma loosen {a b c d} {n:Side} (X:Listing G n) (P : BudgetPoint) (Y : Collection.Source G n)
    (h : Collection.Local X P Y a b) (ha : a ≤ c) (hb : b ≤ d) : Collection.Local X P Y c d := by
  obtain ⟨hF,hK,hM,⟨u,hu,hU⟩,k,hk,hX⟩:=h
  exact ⟨hF,hK,hM,⟨u,hu,fun x=> Cost.enlarge (hU x) ha⟩,k,hk,fun x=> Cost.enlarge (hX x) hb⟩

def hardPrice (m) (β : ℝ) := (1/8 : ℝ)*forecastK A.B.a m R.scout β
include hH hm hl hb
/-- Native coarse step. Can take any `Cash/Price` supplied at this same input,
including the H implicit in the existing repeatable comparison when needed.
Uniform constant in (ii). No assumption about `bar` being the kernel penalty. -/
theorem clearHigh (O : Return.Wood A.B m n) (d : ℕ) :
    Prealigned R (u:=u) (4*d+3) O H
      (Opera.earlyFee (p:=R.expense) A.B N m u.beta)
      (Real.sqrt 2 ^ d * ((Real.sqrt u.beta)⁻¹)^d)
      (hardPrice R m u.beta) := by
  let z := A.B
  let p := A.B.a.budget m
  let j := A.B.a.clock.J (m+1)
  let i := A.B.a.clock.J m
  let x := A.B.a.clock.hatBeta m
  let y := A.B.a.clock.hatBeta (m+1)
  let L := D.L j
  let U := Pressure.Testing.ships A.B N m n
  let t := R.target j i
  let T := R.expense j i
  let g := grow G L x
  have hT:=R.pledging.jewels
  let k:=step_paid A.B.a m; let v:=A.B.valid.pays m
  have hM := hT j x v i k
  obtain ⟨C,d',r,g',b,t',z',Y',q,l,i',⟨N',hv⟩,hK,hp'⟩:= hM.2 _ _ _ U H.laws.data.funds (Opera.protocol A.B hm R.pledging.conducts.full) u H
  obtain ⟨hH',hh,hY,hK'⟩:=R.pledging.peak.large j i k x v
  -- old Armada l used for existing Local cost; use converted for high only
  obtain ⟨hv',ht',he'⟩:= hK' Y' l i' hK N'.balance hp'
  let σ:=A.B.a.params m
  have hσ : σ=X.p.profile i:= params_eq A.B.valid m
  have hE:p.order=(X.p.profile i).order:= congr_arg RG.Stage.order hσ
  have hV:p.power=(X.p.profile i).power:= congr_arg RG.Stage.power hσ
  have hC:p.supportExponent=(X.p.profile i).supportExponent:= congr_arg RG.Stage.supportExponent hσ
  have h₀: preExponent p ≤ T.earn:= by unfold preExponent; rw [hC]; apply R.pledging.agenda j i k|>.1
  have hΞ : preExponent p / (p.B:ℝ) ≤ σ.width/2 := by change (σ.supportExponent+3)/radiusB x ≤ _; rw [hσ]; exact R.pledging.range j x v i k
  have hd:= (R.machine.passes (Q:=fun _ : ℝ=> u) hm (l:=Set.univ) (fun _ _=> ⟨hl,hb⟩)).1.decent
  have hg : U.down.Bounds U.low σ.width σ.paths (A.B.a.clock.loopCap m):=A.B.support.cap _ _ hm.le
  let M:=4*d+3
  let α:=Alpha (A:=A) N m
  let π : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl
  let A':= posting p H; let S:= plusone H π Chi.canonical α
  let S₁:=weigh H π Chi.canonical (arityKeep M) true α
  let S₂:=weigh H π Chi.canonical (arityFilter M) false α
  -- existing keep cost, hard untouched
  have h₁' := Song.loaded (ℓ:=(X.p.profile i).power) p H π Chi.canonical α N' rfl hE.le rfl hg hH h₀ hK hV.le hd hΞ
  have h₁ := attenuate p H π α (arityKeep M) _ _ h₁' (by intro z; unfold arityKeep; split <;> norm_num) true
  have Hh:= Opera.backing A.B R.shape R.pledging.conducts.income hb
  have h₁ : Collection.Local A' p S₁ (Opera.earlyFee (p:=R.expense) A.B N m u.beta) (hardPrice R m u.beta) :=
    loosen _ _ _ h₁ (mul_le_mul_of_nonneg_left (add_le_add_left hp' _) (turnFee_pos _|>.le)) Hh
  -- error cost actual convert beacon paid at window exponent asset
  have h₂' := arityLocal p H π α N' rfl hE.le rfl (X.p.profile i).power hV.le h₀ hH' hv hv' hY ht' hH M
  have hs:y=betaF G x L := PriceCompiler.beta_eq A.B.valid m
  have hy : 1< betaF G x L:= hs ▸ A.B.a.fits.delayed _
  have hB : 0 < u.beta:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))) hb.1
  have hμ:(g^(4*d))⁻¹ ≤ (Real.sqrt 2*(Real.sqrt u.beta)⁻¹)^d := exchange d hy.le hB (hs ▸ hb.2)
  have hR:δE x ≤ 1 := by
    unfold δE Clock.gap
    apply Real.rpow_le_one
    · positivity
    · apply inv_le_one_of_one_le₀
      exact Real.one_le_sqrt.mpr (A.B.a.fits.delayed m).le
    norm_num
  have hPos: 0 < g:= zero_lt_one.trans_le hH'
  have h₂ : Collection.Local A' p S₂ (Real.sqrt 2 ^ d * ((Real.sqrt u.beta)⁻¹)^d) (hardPrice R m u.beta) := loosen _ _ _ h₂' (by
    let c₀:=turnFee p
    let c₁:=away (X.p.profile i)
    let b₀:=heap G (X.p.profile i) (1/16)
    have ht:0 < c₀ := turnFee_pos _
    have hc : c₁=c₀ := by unfold c₁ c₀ away turnFee; rw [hE,hV]
    have hh' : 0 < b₀:= heap_pos _ _ (by norm_num)
    have h₀' : c₀ * b₀ ≤ 1 := by
      unfold b₀ heap; change c₀*(_/c₁) ≤ 1; rw [hc, mul_div_cancel₀ _ ht.ne']
      have he := (Time.authorized G (X.p.profile i)).1; norm_num1 at he ⊢; linarith only [he] -- norm_num at * expensive
    let K := asset T; let m₀:=R.shape.μ j i
    let f₀ := collars G K x (X.p.profile i).order (X.p.profile i).power*(g*salary t L m₀ Y' x (X.p.profile i).order i'*(1-1/2)⁻¹)
    have hf : (g^3)⁻¹*f₀ ≤ b₀ * δE x := by unfold f₀; rw [← mul_assoc]; exact he'
    rw [show grow G _ _ ^ M=g^(4*d)*g^3 from pow_add g (4*d) 3, mul_inv_rev]
    calc
      _ = c₀*((g^(4*d))⁻¹*((g^3)⁻¹*f₀)) := by dsimp only [c₀,f₀]; ring
      _ ≤ c₀*((g^(4*d))⁻¹*(b₀*δE x)) := by gcongr -- hf
      _ = (g^(4*d))⁻¹ * ((c₀*b₀)*δE x) := by ring
      _ ≤ (g^(4*d))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hR (mul_nonneg ht.le hh'.le)).trans ?_) (by positivity)
        simpa using h₀'
      _ = (g^(4*d))⁻¹ := mul_one _
      _ ≤ _ := by rw [← mul_pow]; exact hμ) Hh
  refine ⟨h₁,h₂,?_⟩
  exact Eq.trans (funext fun V=> (Song.forward p H π Chi.canonical α N' O rfl hE.le hg hH V).symm)
    (earlySplit (X:=A') (s:=S) (s₁:=S₁) (s₂:=S₂) (weigh_split ..) rfl _ _ _ _ _ h₁.unweighted h₂.unweighted)

omit hH
/-- existential on the actual input. All constants exactly as listed for any M (internal). -/
theorem stocked (O : Return.Wood A.B m n) (d : ℕ) :
    ∃ H : Guide A.B R.shape N m n u, Opera.Price A.B R.shape N m n u H ∧
      Prealigned R (4*d+3) O H
        (Opera.earlyFee (p:=R.expense) A.B N m u.beta)
        (Real.sqrt 2 ^ d * ((Real.sqrt u.beta)⁻¹)^d)
        (hardPrice R m u.beta) := by
  obtain ⟨H,hH'⟩:= Opera.feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income hl hb
  exact ⟨H,hH', clearHigh R H hH' hm hl hb O d⟩
end YM.RG01.Vacuum
