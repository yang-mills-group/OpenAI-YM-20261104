import YM.Integration.WilsonThermometerWeakPanelBorn
import YM.Integration.WilsonThermometerWeakTwoScalePlacement
import YM.Integration.WilsonThermometerWeakSameRunColumns

/-! The left cylinder is the measured Vane field at its own station. The right is
the complete separately graduated displaced angular source on the same bare law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSameRunCross
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price Next.Rank.Tapes.West Next.Rank.Station Next.Rank.East
open Further.CorrectedLift MergeProof MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato YM.Integration.WilsonLimitConstruction YM.Integration.WilsonPositionThermometerStationNorm
open RG12 RG05Readout Native Address Many Records Harvest
open WilsonThermometerOwnOffsetField WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem moved {d k m χ N p:ℕ} (r:Emblems C d) (hk:k≤N) (hχ:χ≤N) (hm:m≤χ)
    (v:Site ((C).side m p)) (z z₀:Site ((C).side N p))
    (u:(C).label d) (fee:ℝ) (inside:Interior ((center (C).S p hχ 0).chamber 0) (arm R r hk z₀ u))
    (wage:(center (C).S p hχ 0).rootTest ((C).beta N p) (arm R r hk z₀ u)≤fee)
    (margin:z-z₀∈(center (C).S p (hm.trans hχ) 0).margin v (3*Cells.span (C).S hχ p)):
    let T:=center (C).S p (hm.trans hχ) 0
    ∃Y, Interior (T.chamber 0) Y ∧ T.rootTest ((C).beta N p) Y≤fee ∧ T.copy v Y=arm R r hk z u:=by
  intro T
  obtain ⟨Y,hY,price,equal⟩:=Frontier6.Platform.moved_basis R.makes hχ hm v inside wage margin
  refine ⟨Y,hY,price,equal.trans ?_⟩
  funext U
  change ((C).S.a k:ℂ)^d*(C).O N p _ z₀ (Lattice.translate (z-z₀) U)=((C).S.a k:ℂ)^d*(C).O N p _ z U
  rw [R.family.translation];congr 2;abel

private theorem with_pair {N p:ℕ} (T:Tiling ((C).side N p)) (v:Fin 2→Site T.period)
    (apart:v 0≠v 1) (Y:Fin 2 → Config G ((C).side N p)→ℂ)
    (inside:∀i,Interior (T.chamber 0) (Y i)) (q:Fin 2→ℝ)
    (cash:∀i,T.rootTest ((C).beta N p) (Y i)≤q i):
    ‖moment ((C).beta N p) (fun U=>T.copy (v 0) (Y 0) U*T.copy (v 1) (Y 1) U)‖≤q 0*q 1:=by
  have distinct:Function.Injective v:=by intro i j h;fin_cases i<;>fin_cases j<;>simp_all
  have seen:=T.planted (seamless R.makes N p) v distinct Y inside
  simp only [Fin.prod_univ_two] at seen
  exact seen.trans (mul_le_mul (cash 0) (cash 1) (T.root_nonneg _ _) ((T.root_nonneg _ _).trans (cash 0)))

open WilsonThermometerWeakMovedCovers WilsonThermometerWeakJointWidth

theorem original {d D:ℕ} (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (panels:R2I.RG05Joint.AcrossPanels R.kit)
    (f:Extraction.Order) (H:(Cells.standard C).Hierarchy) (grade:Fin (D+1)) (ε:ℝ) (pos:0<ε):
    ∃(P:Fin 3→Tapes.Panel D) (κ:ℝ) (e:ℕ),Checks (P 0).arc (P 1).arc (P 2).arc κ (trays D) D ∧
    ∀a:Fin 3, ∃Q:ℝ,0≤Q ∧ ∀(b h:ℝ),0<b → power (P a).arc b e<h →
    ∀ (x:Fin 2 → E4), (∃j:Axis,x 0 j≠x 1 j) →
    ∀ᶠ k:ℕ in atTop,∀(ℓ:ℕ)(later:k≤ℓ),(A).S.scale ℓ-(A).S.scale k≤Real.log ((A).clock.hatBeta ℓ) →
    Allowed (A) b k → wheel (A) k≤(A).clock.monitor k →
    ∀ᶠ N:ℕ in atTop,∃late:ℓ<N, ∀p,
    let hk:k≤N:=later.trans late.le
    let χ:=width (A) b k
    let hχ:χ≤N:=(wider (A) b k).trans ((before (A) b k).trans hk)
    let T₀:=center (C).S p hχ 0
    ∀ (z:Fin 2→Site ((C).side N p)) (v:Fin 2 → Cover),
    (∀i j,|(C).S.gridPoint k (v i) j-gap (A) h k*x i j|≤16*(C).S.a k) →
    let field:=fun i=>move (C).S p hk (z i) (wrap _ (v i))
    let pivot:=move (C).S p hk (z 1) 0
    ∀{D':ℕ}(V:Vane C D') (j:Fin (D'+1)) (w:(Cells.standard C).Field j),
    j.val=grade.val → V.k=ℓ → V.checked f H D' → ∀(r:Emblems C d)(u:(C).label d)(F:ℝ),
    Interior (T₀.chamber 0) (arm R r hk pivot u) → T₀.rootTest ((C).beta N p) (arm R r hk pivot u)≤F →
    ‖moment ((C).beta N p) (fun U=>(C).O N p (V.wheel.atCut (N,p) j w) (field 0) U*
      arm R r hk (field 1) u U)‖ ≤ (Q*((A).clock.hatBeta ℓ)^ε*(cost C grade*‖w‖))*F:=by
  obtain ⟨P,κ,checks,policy⟩:=WilsonThermometerWeakSameRunColumns.original R simple panels f H D (fun _:Unit=>grade) ε pos
  obtain ⟨s,housing⟩:=WilsonThermometerWeakJointCells.original (C).S
  refine ⟨P,κ,s+1,checks,?_⟩
  intro a
  obtain ⟨money,positive,offer⟩:=policy a
  refine ⟨money (),positive (),?_⟩
  intro b h bp margin x sep
  have ap:0<(P a).arc:=by linarith only [(P a).huge,Nat.cast_nonneg (α:=ℝ) D]
  let U:=power (P a).arc b (s+1)
  have Upos:0≤U:=by
    dsimp [U,power];have t:=le_max_left (4*((P a).arc+5)) (b+5)
    positivity
  obtain ⟨i₀,quoted⟩:=eventually_atTop.mp offer
  filter_upwards [eventually_ge_atTop i₀,WilsonThermometerWeakJointMesh.original R simple shop (P a).arc b ap bp (s+1),
    WilsonThermometerWeakTwoScalePlacement.fee (A) simple U h Upos margin x sep]
      with k ready mesh place ℓ prior near original widthPaid
  let i:=widthSky (A) (P a).arc ℓ;let χ:=width (A) b k
  let m:=min i χ-(s+1)
  obtain ⟨deep0,deep1,scales⟩:=mesh ℓ prior near original widthPaid
  filter_upwards [quoted ℓ (ready.trans prior)] with N source
  obtain ⟨late,due⟩:=source
  refine ⟨late,?_⟩
  intro p hk χ' hχ T₀ z v price field pivot D' V j w hj station checked r u F inside cash
  have hi:i≤N:=(widerSky (A) (P a).arc ℓ).trans ((beforeSky (A) (P a).arc ℓ).trans late.le)
  let dates:Fin 2→ℕ:=![i,χ]
  have avail (a:Fin 2):dates a≤N:=by fin_cases a;exact hi;exact hχ
  have d₀:m+(s+1) ≤ i:=deep0
  have d₁:m+(s+1)≤χ:=deep1
  have deep (a:Fin 2):m+s+1≤dates a:=by
    rw [Nat.add_assoc];fin_cases a;exact d₀;exact d₁
  obtain ⟨far,per⟩:=place m p scales v price
  obtain ⟨α,c₀,c₁,apart,margin₀,margin₁⟩:=housing k m N p hk dates deep avail z v far per
  have m₀:m ≤ i:=le_trans (Nat.le_add_right ..) deep0
  have m₁:m≤χ:=le_trans (Nat.le_add_right ..) deep1
  let tile:=center (C).S p (m₀.trans hi) 0
  obtain ⟨X,hX,qX,atX⟩:=due p m m₀ (fun _=>c₀) (fun _=>field 0+α) V (fun _=>j) (fun _=>w) (fun _=>hj) station checked (fun _=>margin₀) ()
  obtain ⟨Y,hY,qY,atY⟩:=moved R r hk hχ m₁ c₁ (field 1+α) pivot u F inside cash margin₁
  let allot:=money ()*((A).clock.hatBeta ℓ)^ε*(cost C grade*‖w‖)
  have paid:=with_pair R tile ![c₀,c₁] apart ![X,Y] (fun i=>by fin_cases i;exact hX;exact hY)
    ![allot,F] (fun i=>by fin_cases i;exact qX;exact qY)
  change ‖moment ((C).beta N p) (fun U=>tile.copy c₀ X U*tile.copy c₁ Y U)‖≤_ at paid
  rw [atX,atY] at paid
  let upper:=((C).factory d N p).terminal (finer r hk (chunk ( «C» := R.family ) (primaryLetter d) u) (primaryLetter d))
  change ‖moment _ (fun U=>(C).O N p _ (field 0) U*(((C).S.a k:ℂ)^d*(C).O N p upper (field 1) U))‖≤_
  rw [← WilsonThermometerWeakMovedExperiment.shifted R (V.wheel.atCut (N,p) j w) upper (((C).S.a k:ℂ)^d) (field 0) (field 1) α]
  exact paid

end YM.Integration.WilsonThermometerWeakSameRunCross
end
