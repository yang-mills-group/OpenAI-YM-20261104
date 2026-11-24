import YM.LocalTaylorR2.Render
import YM.LocalTaylorR2.Dispatch
import YM.RG01.Survive.Coupled
import YM.RG12.Burst.Cotton
/-!
# Calendar redemption. Issue on existing F756 multiplexer, choosing one
common Decal **before** the physical construction. Provides all-orders
pre-reset Taylor cost estimates beside every `Uses`, Guide and (if
present) the every-phase Final on exactly that construction. No new Family
required to use arbitrary union of finite queries. (Later reclosure with
fresh addresses will need its own geometric and normalization costs.)
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
open Daisy.Charity.RG12

def loss (j : ℕ) := (j+1:ℝ)⁻¹
def ticketD (G:Gauge) : Decal G where
  rub P Q E L W μ o U j x:= (∃ D:RG.Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j)→∀ l:ℕ,l≤j →
    Written Q L W μ x (loss j) (E.one/2) (Push.Local.turnCost U.order U.power) U.order U.power l o Chi.canonical
  good P Q E:= by
    obtain ⟨n,hn⟩:= choosesTail P Q E; refine ⟨n,fun L h W μ o U j _ hw hμ=> ?_⟩
    by_cases he: ∃ D:RG.Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap; · exact Eventually.of_forall (fun _ hz=> (he hz).elim)
    have hm(l:Fin (j+1)):=hn L h W μ o U.order U.power l.val (loss j) (Push.Local.turnCost U.order U.power) Chi.canonical hw hμ (by unfold loss; positivity) he
    exact (eventually_all.mpr hm).mono fun _ hp _ k hk=> hp (⟨k,Nat.lt_succ_of_le hk⟩:Fin _)

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

lemma fullLocal {c:Lattice.Side}{p:BudgetPoint}{J:Collection.Listing G c}{v:Collection.Source G c}{a e l w:ℝ}(h:Collection.Local J p v a l)(hu:a ≤ e)(hv:l≤w): Collection.Local J p v e w:= by
  obtain ⟨hF,hK,hM,⟨u,hu',hU⟩,k,hk,hX⟩:=h
  exact ⟨hF,hK,hM,⟨u,hu',fun x=> Cost.enlarge (hU x) hu⟩,k,hk,fun x=> Cost.enlarge (hX x) hv⟩
include O hH hm hl hb
lemma grounded : Collection.Local Z! b C! Ef Wg:= by
  have hV := choiceLocal R H O hH hm hl hb (fun _=>False) 0 le_rfl (fun _ h=>h.elim)
  suffices he : shelf R H (fun _=>False) false=C! by rw [← he]; exact hV.1
  have hl {A' B: Collection.Source G (A.B.a.S.side m n)}(h:A'.logRead=B.logRead)(hp:A'.hardRead=B.hardRead): A'=B:=by cases A'; cases B; congr
  refine hl ?_ rfl
  funext i; unfold shelf; rw [weightedReading]
  change weightAt H ι (chooseMark R H (fun _=> False) false) (!false) i • (C!).logRead i=(C!).logRead i
  unfold weightAt; cases (pennant H i).2 <;> simp [chooseMark]

omit hl hb
end YM.LocalTaylorR2.CalendarStep
