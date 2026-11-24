import YM.RG01.Survive.Render
import YM.RG01.Vacuum.Actual
/-!
# Conditional *actual* low primitive adapter

Remaining signature on one physical Floral step: low survivors' integrated
kernels and last error meet LeafReady at the common directory on the same
step, tariff allocated a second-tree share with open power tests. Then the
vacuum high-order analytic + exceptional remainder contributes only this
EBound at supported Mask derivatives, and the full density is exactly the
rendered log plus that error with all hard partners. No premise of *matching
coefficients*. Need separate IDs for the `<` filtered ballot `x_t` (and reclosure
for new gauge completions). Neither presumes nor provides convergence to final
Schwinger/Wightman or comparisons in another scheme. This file doesn't supply
the leaf estimates on Floral; inspect implementations in Survive and production
notes for open status. No affine/scalar or kinetic readout; the originating
path in `earlyValue` remains at physical fine β, and the γ correction there
is still tracked for re-expression after this comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Survive
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)} (H : Guide A.B R.shape N m n u) (O:Return.Wood A.B m n)

def gradeCap (r:ℕ):ℕ:=3+4*r
def lengthCap (r:ℕ):ℝ:=((1+2*r:ℕ):ℝ)*Pressure.Stores.till (A.B.a.clock.hatBeta m)

theorem complement (k : H.fragrances)(d) : short (gradeCap d) (lengthCap (A:=A) (m:=m) d) k ↔ ¬Vacuum.importedTail R H d k:= by
  unfold short Vacuum.importedTail
  push Not
  exact and_congr Iff.rfl (and_congr (by omega) Iff.rfl)

abbrev identityX:Alliance H H 1 0:=Match.staple rfl rfl rfl
abbrev gShell:=A.B.kin.alpha N m
abbrev logAt (r:ℕ) {K : ℕ}(x:Expansions H K)(retain:Bool) :=
    rebate (χ:=Chi.canonical) H (identityX H) (gradeCap (r+1)) (lengthCap (A:=A) (m:=m) (r+1)) (gShell (A:=A) (N:=N) (m:=m)) x retain (fun k=> if retain then ¬r+1≤k else r+1≤k)
abbrev standard : Listing G (A.B.a.S.side m n):=Song.posting (A.B.a.budget m) H
abbrev coarse (v:Collection.Source G (A.B.a.S.side m n)):=earlyValue (standard H) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) v u.beta
    (Song.weighty H Chi.canonical O) (A.B.kin.alpha N m)

-- compose two EBounds
private lemma join {c : Lattice.Side}{p:BudgetPoint} (A:Listing G c)(K V : Collection.Source G c)(v:Collection.Source G c)(hx:v.logRead=K.logRead+V.logRead){η β W :ℝ}
    (hK:Collection.Local A p K η W)(hV:Collection.Local A p V β W) :
    (A.read v).EBound p (η+β) ∧
      Vacuum.exponentialShare A p V*Vacuum.exponentialShare A p K= Vacuum.exponentialShare A p v := by
  constructor
  · obtain ⟨a,ha,h₁⟩:=hK.unweighted; obtain ⟨b,hb,h₂⟩:=hV.unweighted
    refine ⟨fun i=>a i+b i,fun i=> ?_,fun i=>?_⟩
    · change p.supBounds _ _ _ (a i+b i)
      have h:= CouplingShape.sup_sub (hK.smooth i) (CouplingShape.reg_scale (-1) (hV.smooth i)) (ha i) (CouplingShape.sup_scale (-1) (hb i)); simp only [neg_one_smul, sub_neg_eq_add, abs_neg,abs_one,one_mul] at h; unfold Listing.read; dsimp only; rw [hx]; exact h
    convert! budget_plus (h₁ i) (h₂ i) using 1; ext j; dsimp [Listing.read,BudgetPoint.mass]; split_ifs <;> ring
  -- no K. use same algebra via density logs.`earlySplit` not exposing additive.
  funext U
  have he (x : Collection.Source G c){c d:ℝ}(h: Collection.Local A p x c d): Dominated
      (fun i (V: Config G _)=> masked p.threshold (A.reg i).support (x.logRead i) V):= by
    obtain ⟨e,ht,hE⟩:=Activities.E_total h.unweighted
    refine ⟨e,ht,fun i V=>?_⟩; dsimp only
    by_cases hg:Healthy p.threshold (A.reg i).support V
    · rw [masked_eq _ _ _ _ hg]; exact (hE i).2 V hg [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hg,norm_zero]; exact (hE i).1
  dsimp only [Pi.mul_apply,Vacuum.exponentialShare,Activities.additive,Activities.regularOccurrence,Listing.read]
  rw [← Real.exp_add,← neg_add,add_comm (∑' _,_) (∑' _,_), ← Summable.tsum_add ((he _ hK).summable U) ((he _ hV).summable U)]
  apply congr_arg (fun a:ℝ=>Real.exp (-a)); apply tsum_congr; intro i; rw [hx]
  by_cases hS:Healthy p.threshold (A.reg i).support U <;> simp [hS]

variable {K j p : ℕ} {x:Expansions H K} {v ρ w δ β a : ℝ}{U:H.ThinP→ Orders K→ℝ}{z : H.ThinP→ℝ}
    (hH: Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : RG.Shoot.Lives A.B.bake N (m+1) n u) (hb: u.beta∈ RG.Shoot.band A.B.a (m+1))
    (h:LeafReady Chi.canonical (gradeCap (K+1)) (lengthCap (m:=m) (A:=A) (K+1)) x v j U z ρ)
    (hi: (A.B.a.params m).order≤j) (hr:(A.B.a.params m).power ≤ p)(q:ℝ)
    (hq:0≤q)(hS:Sailor G (A.B.a.budget m).threshold q j)(hs:j*q≤v)(hv:0<v)
    (hA: Quotes.preExponent (A.B.a.budget m)≤a) (hδ:0<δ)
    (hY:Ready H.smallAt (radiusB (A.B.a.clock.hatBeta m)) (fun i=>2^j*z i) (a+δ) w δ β)
include hH hm hl hb h hi hr hq hS hs hv hA hδ hY

def fusedError := {(logAt H K x false) with logRead:= (Vacuum.shelf R H (Vacuum.importedTail R H (K+1)) true).logRead + (logAt H K x false).logRead}

theorem coupling {c : ℝ}
    (hK:Real.exp (-(Vacuum.cashMark R m))*Vacuum.voucher (A:=A) m^3≤c*((Real.sqrt u.beta)⁻¹)^(K+1)):
    let fee:=readerCost (G:=G) (A.B.a.budget m) j p ρ δ (A.B.a.clock.hatBeta m) w β (K+1)
    let ℓ:= fusedError (R:=R) (H:=H) (x:=x)
    let Z:=standard H
    let bill:= (Real.sqrt 2^(K+1)+c)*(Real.sqrt u.beta)⁻¹^(K+1)
    ((A.B.a.clock.op m n).push u.beta u.eval = coarse H O (logAt H K x true)*Vacuum.exponentialShare (standard H) (A.B.a.budget m) ℓ) ∧
      (Z.read ℓ).EBound (A.B.a.budget m) (bill+fee) ∧ (Z.read ℓ).KBound (A.B.a.budget m) (A.B.a.clock.forcedAllowance m) := by
  intro fee ℓ Z bill
  let C:=A.B.a.clock; let B:=A.B.a.budget m
  let r:=K+1
  let Ae := identityX H; let D':=Vacuum.importedTail R H r; let E:= Vacuum.shelf R H D' true; let M:= Vacuum.shelf R H D' false
  have hD:=Vacuum.rare R H O hH hm hl hb r hK
  unfold Vacuum.Decision at hD; dsimp only at hD
  let γ:=gShell (N:=N) (m:=m) (A:=A)
  have he:M= remain H (χ:=Chi.canonical) Ae (gradeCap r) (lengthCap (A:=A) (m:=m) r) γ:= by
    unfold M D' Vacuum.shelf remain
    congr! 2
    rename_i z
    by_cases hv:Vacuum.importedTail R H r z
    · simp [Vacuum.chooseMark,hv,(complement H z r).not.mpr (not_not.mpr hv)]
    simp [Vacuum.chooseMark,hv,(complement H z r).mpr hv]
  let Y:= logAt H K x false; let F:= logAt H K x true
  have hy' := survival H h Ae γ B rfl rfl hi p hr q hq hS hs hv hA hδ hY K le_rfl (he ▸ (show Collection.Local Z B M _ _ from hD.1))
    (A.B.kin.path N m) (A.B.a.params m).clip u.beta (Song.weighty H Chi.canonical O) γ
  dsimp only at hy'
  change (remain H (χ:=Chi.canonical) Ae (gradeCap r) (lengthCap (A:=A) (m:=m) r) γ).logRead = F.logRead+Y.logRead ∧ _ at hy'
  rw [← he] at hy' -- maybe only logRead
  obtain ⟨ht',hm',hw',hY',hr',hφ⟩:= hy'
  have hd : ℓ.logRead=E.logRead+Y.logRead:=rfl
  obtain ⟨he',hx'⟩:= join Z E Y ℓ hd hD.2.1 hY'
  refine ⟨?_ ,he',?_⟩
  · change _=coarse H O F * _
    exact Eq.trans hD.2.2 (Eq.trans (congr_arg₂ (·*·) hφ (rfl : Vacuum.exponentialShare Z B E=Vacuum.exponentialShare Z B E)) (by rw [mul_assoc]; exact congr_arg₂ (·*·) rfl hx'))
  have hh:= Vacuum.localK hD.2.1
  obtain ⟨b,he,hL⟩:=hh; exact ⟨b,he,hL⟩

end YM.RG01.Survive
