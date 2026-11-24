import YM.RG01.Reinsert
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-! # Purchase arbitrary occurrence orders on the same physical Teller

No reissuing the schedule. Notice the arbitrary order **at the same** p.power,
p.order and exponent+3 even when demands are increasing along the UV trajectory;
this clause requires retaining the unused beacon moment of the existing proof and
spending it before orbit averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Physical
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Input Time Org Supply
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Greenbelt Match Song
open Roof Roost ThroughLaunch Progress.DirectedRecipe Stock Opera PriceCompiler Pressure.Testing
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (hG : G.Simple) {M : Metals G} {D:Rolls M.p} {A : Alloy M D}
  (X : Factor A) {N m n : ℕ}
local notation "lv"=> A.B.a
local notation "FINE"=> A.B.a.S.side (m+1) n
local notation "XXm" => A.B.a.clock.hatBeta m
local notation "BP"=> (A.B.a.budget m)
local notation "J_f"=> A.B.a.clock.J (m+1)
local notation "J_c"=> A.B.a.clock.J m
local notation "YY"=> X.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "φ"=> A.B.kin.alpha N m

variable (Q : RG.Rep G (A.B.a.S.side (m+1) n)) (hm:m<N) (hq:Lives A.B.bake N (m+1) n Q) (hx:Q.beta∈band A.B.a (m+1))
variable (H : Guide A.B X.shape N m n Q)
local notation "UU"=> M.p.profile (A.B.a.clock.J m)
local notation "GROW_" => grow G (D.L (J_f)) (XXm)
local notation "Opr"=> A.B.a.clock.op m n

lemma turn_eq : turnFee (A.B.a.budget m) = Height.away (M.p.profile (A.B.a.clock.J m)) := by
  have h:= params_eq A.B.valid m
  unfold turnFee Height.away
  rw [show (BP).order=(UU).order from congr_arg Stage.order h,show (BP).power=(UU).power from congr_arg Stage.power h]

include Q hm X H
/-- The *same* full canonical dictionary as the exact push can be cut at
arbitrary beacon weight. This does not account for low degree log terms that
must also be estimated within that cut. -/
lemma purchase :
    let Z:=posting (BP) H; let r:Alliance H H 1 0:= Match.staple rfl rfl rfl
    1≤ (GROW_) ∧ (GROW_)^3 ≤ Real.exp ((YY).ε*Stores.till (XXm)) ∧
      (GROW_)^3 ≤ Real.exp ((YY).mark (D.L (J_f)) (X.shape.μ (J_f) (J_c)) (XXm)) ∧
      ∀ (test:H.fragrances→Prop) (K:ℝ), 0<K → (∀ z,test z→ K≤ Height.beacon H z) →
        List.Budget (BP) Z.reg ((List.tail (χ:=Chi.canonical) r test).logRead)
          ( ((GROW_)^3/K) * forecastE A.B.a m) := by
  intro Z acct
  let k:=step_paid lv m; let v:=A.B.valid.pays m
  let hw:= H.laws.data.funds; let hShel:= X.pledging
  let hStamp:= Opera.protocol A.B hm hShel.conducts.full (n:=n)
  have hH:= hShel.jewels (J_f) (XXm) v (J_c) k
  obtain ⟨C,d,r,g,b,t,z,Y'',q,l,i,⟨N',hv⟩,hK,hp'⟩:= hH.2 _ _ (Opr) (ships A.B N m n) hw hStamp Q H
  obtain ⟨hH',hh,hY,hK'⟩:= hShel.peak.large (J_f) (J_c) k (XXm) v
  obtain ⟨hv',ht',he'⟩:= hK' Y'' l i hK N'.balance hp'
  have hσ:= params_eq A.B.valid m
  have hS:(BP).supportExponent=(UU).supportExponent:= congr_arg RG.Stage.supportExponent hσ
  have ho:(BP).order=(UU).order:= congr_arg RG.Stage.order hσ; have hV:(BP).power=(UU).power:= congr_arg RG.Stage.power hσ
  have h' : preExponent (BP) ≤ (X.expense (J_f) (J_c)).earn:= by unfold preExponent; rw [hS]; exact (hShel.agenda _ _ k).1
  refine ⟨hH',hH.1,hh,fun test K hk Htest=> ?_⟩
  apply (List.license acct N' (BP) (UU).power rfl ho.le hV.le rfl h' hH' hv hv' hY ht' test K hk Htest).loosen
  let Y:=asset (X.expense (J_f) (J_c)) -- binder value of y?
  let b:= (collars G Y (XXm) (UU).order (UU).power*((GROW_)*salary (YY) (D.L (J_f)) (X.shape.μ (J_f) (J_c)) Y'' (XXm) (UU).order i*(1-1/2)⁻¹))
  let L:= ((GROW_):ℝ)^3
  change turnFee (BP)*(K⁻¹*b) ≤ _
  have hl:0<L:=by unfold L; positivity
  have hB : L⁻¹*b ≤ Height.heap G (UU) (1/16)*δE (XXm):=by
    convert he' using 1; ring
  have hx : b ≤ L*(Height.heap G (UU) (1/16)*δE (XXm)):= by
    exact (le_of_eq (show b=L*(L⁻¹*b) by simp [hl.ne'])).trans (mul_le_mul_of_nonneg_left hB hl.le)
  let V := turnFee (BP)
  have hV0:0<V:=turnFee_pos _
  have hV1 : V=Height.away (UU):= turn_eq (A:=A)
  have hz : forecastE A.B.a m=Time.credit G (UU)*δE (XXm):= by
    unfold Time.forecastE; rw [hσ]; rfl
  have hx0: 0≤forecastE A.B.a m:= by rw [hz]; unfold δE Clock.gap; have hz:0<credit G (UU):= Time.credit_pos ..; positivity
  change V *_ ≤ _
  calc
    _ ≤ V * (K⁻¹*(L*(Height.heap G (UU) (1/16)*δE (XXm)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (inv_pos.mpr hk).le) hV0.le
    _ = (L/K)*((1/16)*forecastE A.B.a m) := by
      unfold Height.heap
      rw [← hV1,hz]; field_simp
    _ ≤ (L/K)*forecastE A.B.a m := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hx0 (by norm_num)) (by positivity)

/-- Actual Push expressed as the controlled split representation after the
cluster expansion, before affine reset and canonical capture. c:Side is the
coarse side m,n. No Tag averaging on a different denominator. -/
structure Archive (A : Alloy M D) (N m n:ℕ) (Q : RG.Rep G (A.B.a.S.side (m+1) n))
    (X : Factor A) (K : ℝ) where
  names : Guide A.B X.shape N m n Q
  scalar : ℝ
  culled : names.fragrances → Prop
  registered z : culled z → K ≤ beacon names z
  /-- same-book supplies for front subtractions (error bound in `estimate`) -/
  volume : ℝ
  actual :
    let R := Match.staple rfl rfl rfl (H:=names) (J:=names)
    let Z:= posting (A.B.a.budget m) names
    Collection.Local Z (A.B.a.budget m) (plusone names R Chi.canonical (A.B.kin.alpha N m)) volume
      ((1/8)*Time.forecastK A.B.a m X.scout Q.beta)
  source :
    let R := Match.staple rfl rfl rfl (H:=names) (J:=names)
    let Z:= posting (A.B.a.budget m) names
    let U := A.B.kin.path N m
    let c := (A.B.a.params m).clip
    (A.B.a.clock.op m n).push Q.beta Q.eval=
      earlyValue Z U c (A.B.a.budget m) (plusone names R Chi.canonical (A.B.kin.alpha N m))
        Q.beta scalar (A.B.kin.alpha N m)
  estimate :
    let R := Match.staple rfl rfl rfl (H:=names) (J:=names)
    let Z:= posting (A.B.a.budget m) names
    List.Budget (A.B.a.budget m) Z.reg
      ((List.tail (χ:=Chi.canonical) R culled).logRead)
      (((grow G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))^3/K)*
        forecastE A.B.a m)

include hx hq
lemma enact (h : Price A.B X.shape N m n Q H) (F: Tree.Forest (Opr).ratio)
    (test : H.fragrances→Prop) (K : ℝ) (hk : 0<K)
    (ht : ∀ z, test z → K ≤ beacon H z):
    ∃ a:Archive A N m n Q X K, a.names=H ∧ a.scalar=weighty H Chi.canonical F ∧
      HEq a.culled test := by
  let hShel := X.pledging
  let d:= Opera.forum A.B X.shape (m:=m) (n:=n)
  let U : Alliance H H 1 0 := Match.staple rfl rfl rfl
  obtain ⟨he,hV⟩:= Opera.symphony A.B X.shape hm hShel.conducts.full hShel.conducts.income
    (fun i j h=> (hShel.agenda i j h).1) X.machine hShel.range hq hx F d H H h U
  have hg:= Return.earnings A.B N F d Chi.canonical (radiusW X.rider) X.machine.ring X.machine.bill hm Q hq hx
  let b := Opera.earlyFee (p:=X.expense) A.B N m Q.beta
  exact ⟨⟨H,_,test,ht,b,hV,hg.2.2.trans he, (purchase X Q hm H).2.2.2 test K hk ht⟩,rfl,rfl,HEq.rfl⟩

end YM.RG01.Physical
