import YM.LocalTaylorR2.Send
/-!
# Pre-reset readout **before** the actual nonlinear reclosure

Keep the scalar term and quadratic readout of this representation
separate. Affine statements on unmasked centered germs, not asserting
invariance of affine readout after realignment or in a different scheme.
Numerical uncertainty of quadratic projection retains TWO inverse
threshold powers, of scalar per site BEFORE the extensive conversion.
-/
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
open UVNext.CouplingReset Averaging
section arithmetic
variable {c:Lattice.Side}{p:BudgetPoint}{J:Collection.Listing G c}{v w y:Collection.Source G c}{u A B Z C Q:ℝ}
    (h0:G.Simple)(h:Collection.Local J p v A Z)(he:Collection.Local J p w B C)(ht:Collection.Local J p y Q u)(hs:v.logRead=w.logRead+y.logRead)
include h he hs h0
lemma kineticFee : Averaging.delta (J.read v)- Averaging.delta (J.read w)= Averaging.delta (J.read y) := by
  unfold Averaging.delta Averaging.total; rw [← (h.projects.seriesAt h0 ..).tsum_sub (he.projects.seriesAt h0 ..)]; apply tsum_congr; intro i
  unfold censusAt; dsimp only [Listing.read]; split
  · rw [show y.logRead i=v.logRead i - w.logRead i from eq_sub_of_add_eq' (show _ from Eq.symm (congr_fun hs i)), projection_sub _ (h.smooth i) (he.smooth i)]
  simp

omit h he hs
include ht
lemma vac_ledger : |Collection.vac y 0| ≤ Q := by
  obtain ⟨b,hb,H⟩:=ht.unweighted
  have hu:= ht.raw_sum h0 1|>.1
  let f(x:Site c)(i:ℕ):= if (J.reg i).site=x then ‖y.logRead i 1‖ else 0
  unfold Collection.vac; rw [zero_sub, abs_neg,abs_div,abs_of_pos (sites_pos _),div_le_iff₀ (sites_pos _)]
  apply (norm_tsum_le_tsum_norm hu.norm).trans
  have hx x : Summable (f x):= hu.norm.of_nonneg_of_le (by intro i; unfold f; split; exact norm_nonneg _; exact le_rfl) (by intro i; unfold f; split; exact le_rfl; exact norm_nonneg _)
  have he i: ‖y.logRead i 1‖=∑ x:Site c, f x i:=by simp [f]
  calc
    _ = ∑ x:Site c, ∑' i,f x i:=by rw [← Summable.tsum_finsetSum (fun i (_:i∈univ)=> hx i)]; exact tsum_congr he
    _ ≤ ∑ _x:Site c,Q:= Finset.sum_le_sum fun i _=> (Summable.tsum_le_tsum (fun j=> ?_) (hx i) (H i).2.1).trans (H i).2.2
    _ = _ := by simp [UVNext.CouplingReset.sites,mul_comm]
  dsimp only [Listing.read,f]; split
  next hx =>
    have hh:‖y.logRead j 1‖≤ b j := (hb j).2 1 (flat_ok ..) [] (by simp) (by simp)
    exact hh.trans (p.loMass _ _ (hb j).1)
  exact le_rfl

include h he hs
omit h in
lemma scalarFee (t:ℝ): Collection.vac v t- Collection.vac w t=Collection.vac y 0 := by
  unfold Collection.vac; rw [hs]; simp only [Pi.add_apply]; rw [Summable.tsum_add (he.raw_sum h0 1|>.1) (ht.raw_sum h0 1|>.1)]; ring
end arithmetic
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
include hH hl hb O hm
lemma mails (hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay) (l:ℕ) (hy:l ≤ j₁) (ε:ℝ)(hε:loss j₁ ≤ ε)(h0:G.Simple):
    let x:= interpret R H l true
    let y:= interpret R H l false
    let Δ:= Averaging.delta ((Z!).read y)
    let err:= xF^requested (l+1) ε
    let t:= Song.weighty H Chi.canonical O
    Collection.Local Z! b y err Wg ∧ (b).threshold^2*|Δ| ≤ err ∧
      |Collection.vac y 0|≤err ∧
      Collection.vac (C!) t- Collection.vac x t=Collection.vac y 0 ∧
      Averaging.delta ((Z!).read (C!))-Averaging.delta ((Z!).read x)=Δ:= by
  obtain ⟨hx,hj,-,-,-,hA,hB,he⟩:=transmit R H O hH hm hl hb hp l hy ε hε
  intro x y Δ err t
  have hz : Collection.Local Z! b y err Wg:= by unfold y interpret; simpa only [Bool.false_eq_true,ite_false] using! he (fun i=> l+1 ≤ i) (l+1) le_rfl (fun _ h=> h)
  exact ⟨hz,Averaging.delta_bound h0 hz.projects,vac_ledger h0 hz,scalarFee h0 hB hz hx t, kineticFee h0 hA hB hx⟩
end YM.LocalTaylorR2.CalendarStep
