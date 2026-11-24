import YM.QuadraticLocal.Vacuum.Grant
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext Repeat Height Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P} {μ a:ℝ}
local notation "Z" => betaF
lemma burnsWith (Q : YM.ConnectedActivityE6.Target G P) (π : ℕ) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W),
    0<W → 0<μ → Q.rate < -(3/8:ℝ) → ∀ j n χ, ∀ᶠ x:ℝ in atTop,
    ∀ (c' f : Side) (S:StepData c' f) (T:Tube G S), Works P L x S T → Stamp T → ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R), ∀ τπ:Raw.Multiplier, Raw.Tollable τπ P T x R →
      ∃ (C' d v t A b r B q : ℝ) (k : ℕ) (N:Captain H j C' d v t A b r B q k χ), Lions τπ (Burn.alt π) N.conduit ∧
         ∀ (w:ℝ)(M:Set ℕ), 1≤w→(∀ i, i∉M→ w≤τπ.weight i) → Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>if tiredT H (Burn.typeT M π) (Burn.alt π) z then N.markΦ z n else 0) X.earn ((grow G L x ^ Burn.alt π)⁻¹+(grow G L x ^3*w)⁻¹) := by
  obtain ⟨m,hm⟩:= mountW (Burn.alt π) P Q; refine ⟨m,fun L hL X W μ c o hW hμ hR j n χ=> ?_⟩
  by_cases Hs : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c f S T h=> (Hs ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:=Hs
  obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j χ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  -- allocate degree prices before volume
  let f' x:= grow G L x; have hf := Rate.power (G:=G) (L:=L) (a:=3/8)
  have hh' : 3/8+Q.rate < 0:= (by linarith)
  have hev:=(hf.mul (hg n 0)).below hh' 1 zero_lt_one
  have hp:= Q.rate_root L hμ (β:=1) (C:=0) -- notation
  filter_upwards [H,hg n 0 X.wanting X.reach,hK,bigMark (Burn.alt π) Q L hμ, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1, pressureYoung G L (i:=Q.δ) hp (by linarith),pressureYoung G L (i:=y) (stipulatedS Q L hμ hB k j) (by linarith), hev] with x h hh hA he' hx hv hs hr c f S T hW hxP R I τπ hτπ
  obtain ⟨N,hN⟩:= h c f S T (hW.patch hF hX) hxP R _ I τπ hτπ
  simp only [pow_zero,mul_one] at hh hr
  refine ⟨_,_,_,_,_,_,_,_,_,k,N,hN,fun w M hw hY v=>?_⟩ -- duplicate x
  let u := v -- position
  let o:=f' x; have hp':1≤ f' x:= Real.one_le_rpow hx (by norm_num)
  apply budget_loosen (Height.chargedHit N hp' n hA hv hs hN w hw hY he'.1 he'.2 _) -- arg order inspect
  apply mul_le_of_le_one_right
  · have he:=zero_le_one.trans hp'; have hη:=zero_lt_one.trans_le hw; change 0 ≤ (f' x ^_)⁻¹+(f' x^_*_)⁻¹; positivity
  apply le_trans _ hr
  -- hr is | f*x * ... | ≤ _
  apply le_trans _ (le_abs_self _); apply le_of_eq; unfold grow; ring
end YM.AllOrder.High
