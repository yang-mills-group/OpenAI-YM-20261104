import YM.LocalTaylorR2.Ingress
/-! # Strict consumer at the RG01 interface as well (arity and length-filtered)
 Do *not* identify the two Taylor comparisons; this one omits additional
 terms beyond the stated Taylor error using another verification purchase. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.CalendarStep
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01.Vacuum Tail RG01.Survive
variable {G : Gauge}
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) {m n N : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)}
local notation "b" => A.B.a.budget m
local notation "β" => A.B.a.clock.hatBeta m
local notation "α" => (Alpha (A:=A) N m)
local notation "j₀" => A.B.a.clock.J m
local notation "j₁" => A.B.a.clock.J (m+1)
variable (H:Guide A.B R.shape N m n u) (O: Return.Wood A.B m n)
    (hH:Opera.Price A.B R.shape N m n u H)(hm:m<N)(hl:Lives A.B.bake N (m+1) n u)(hb:u.beta∈band A.B.a (m+1))
set_option quotPrecheck false
local notation "h₀"=> R.target (j₁) (j₀)
local notation "Γ"=> R.expense (j₁) (j₀)
local notation "Wg"=>A.B.a.clock.forcedAllowance m
local notation "Ef"=>Opera.earlyFee (p:=R.expense) A.B N m u.beta
local notation "L!"=>D.L (j₁)
local notation "Z!" => Song.posting (b) H
local notation "ι" => (RG01.Survive.identityX H)
local notation "C!"=>plusone H ι Chi.canonical α
local notation "xF" => A.B.a.clock.hatBeta (m+1)
-- universal constant on all R (including off Uses branch) with its exact Invoice
lemma shortRoute (hG:G.Simple) (hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay) (l:ℕ):
    ∃ c:ℝ, 0≤c ∧ ∀ (m n N:ℕ) (u:RG.Rep G (A.B.a.S.side (m+1) n)) (H:Guide A.B R.shape N m n u) (O:Return.Wood A.B m n),
      Opera.Price A.B R.shape N m n u H → m<N → Lives A.B.bake N (m+1) n u → u.beta∈band A.B.a (m+1) → l ≤ A.B.a.clock.J (m+1) →
      let v:= logAt H l (K:=l) (Candle.sprig H Chi.canonical) true
      let P:= standard H
      let ℓ:= fusedError (R:=R) (H:=H) (K:=l) (x:=Candle.sprig H Chi.canonical)
      let s:= A.B.a.clock.hatBeta (m+1); let z:=loss (A.B.a.clock.J (m+1))
      let w:=A.B.a.budget m; let g:= (Real.sqrt u.beta)⁻¹; let t:=(Real.sqrt 2^(l+1)+c)*g^(l+1)
      (A.B.a.clock.op m n).push u.beta u.eval=coarse H O v *exponentialShare P w ℓ ∧
        (P.read ℓ).EBound w (t+s^requested (l+1) z) ∧ (P.read ℓ).KBound w (A.B.a.clock.forcedAllowance m):=by
   obtain ⟨c,hc,h⟩:=markCurrency R hG (l+1); refine ⟨c,hc,?_⟩; intro m n N u H O hH hm hl hb hx v P y s z B g t
   obtain ⟨C',d',v',t',A₀,a,r,B',q,H₁,H₂,e,F',θ,i,N',hX⟩:= deliver R H hm hp l hx z le_rfl
   have he: preExponent B ≤ (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn:=by unfold B preExponent; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)|>.1)
   obtain ⟨ht,hh,hL⟩:= RG01.Survive.coupling (R:=R) H O hH hm hl hb (hX.probed.consumer _ _) le_rfl (p:=(A.B.a.params m).power) le_rfl q hX.prices.1 hX.launch hX.prices.2 hX.nonzero he (half_pos ((R.expense _ _).first)) hX.buoy (h m N hm u.beta hb)
   obtain ⟨u₁,hu,hK⟩:= hh
   exact ⟨ht,⟨u₁,hu,fun i=> budget_loosen (hK i) (add_le_add_right (hX.charges _ le_rfl) t)⟩,hL⟩
end YM.LocalTaylorR2.CalendarStep
