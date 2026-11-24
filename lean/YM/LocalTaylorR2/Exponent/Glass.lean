import YM.LocalTaylorR2.Exponent.Retro
import YM.LocalTaylorR2.Mesh.Classroom
import YM.LocalTaylorR2.Receipt
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
namespace YM.LocalTaylorR2.Exponent
open CalendarStep
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

variable (Ξ:Observatory G)
def reckon  : Decal G where
  rub P Q E L W μ o U j x:= (∃ D:RG.Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j)→∀ l:ℕ,l≤j →
    ManifestX Ξ Q L W μ x (loss j) (E.one/2) (Push.Local.turnCost U.order U.power) U.order U.power l o Chi.canonical
  good P Q E:= by
    obtain ⟨n,hn⟩:= Exponent.launchRevenue Ξ P Q E; refine ⟨n,fun L h W μ o U j _ hw hμ=> ?_⟩
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
local notation "μ" => R.shape.μ j₁ j₀
local notation "order" => (b).order
local notation "σ" => (b).power
local notation "δ" => ((Γ).one / 2)
local notation "xF" => A.B.a.clock.hatBeta (m+1)
local notation "χ" => Chi.canonical
local notation "Tx" => A.B.a.clock.op m n
-- Use all letters of Orders l through `i`; flavors & credential.
structure Counter (l:ℕ) (H:Guide A.B R.shape N m n u)(ε v q e t:ℝ) (y : H.ThinP→Orders l→ℝ) (z:H.ThinP→ℝ):Prop where
    probed : ReadyAll χ (Mesh.issue H (Ξ.upgrade H l) χ) v (order) y z t
    buoy : Ready H.smallAt (radiusB β) (fun i=>2^order*z i) ((Γ).earn+δ) e δ (1/2)
    charges (i:ℕ) : i ≤ l+1 → readerCost (G:=G) b order σ t δ β e (1/2) i ≤ xF^(requested i ε)
    nonzero : 0<v
    launch : Sailor G (b).threshold q order
    prices : 0≤q ∧ order*q≤v
include hm
lemma polity (hp:Mallow.RG12.Earned (reckon Ξ) R.shape A.delay) (l:ℕ)(hy:l ≤ j₁)(ε:ℝ)(hε: loss j₁ ≤ ε) :
    ∃ (C' d v w A₀ a r B q D' x w' t θ:ℝ) (i:ℕ) (N':Captain H order C' d v w A₀ a r B q (i+order) χ),
       Counter Ξ R l H ε v q w' t (Exponent.heavies N' D' x θ t) (Exponent.resultN N' θ (l+1:ℝ) t D' x l) := by
   let μ' := μ
   have hv:= H.laws.data.funds
   have hu:=hp _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) ⟨(Tx).patch,hv.funds.kernel,hv.length_eq,hv.funds.atStep⟩ l hy
   have hf := params_eq A.B.valid m
   have hh : ManifestX Ξ h₀ L! (R.walls j₁ j₀) μ' β (loss j₁) δ (turnFee b) order σ l (R.shape.o j₁ j₀) χ := by
     change ManifestX Ξ _ _ _ _ _ _ _ (Push.Local.turnCost (A.B.a.params m).order (A.B.a.params m).power) (A.B.a.params m).order (A.B.a.params m).power _ _ _; rw [hf]; exact hu
   obtain ⟨A₀,a,C',x,d,v,w,r,B,K,q,t,y,w',θ,i,k,hh,H'⟩:= hh
   obtain ⟨N',hB,hX,hCr,H0,j₂,hI⟩:=hh.chooses _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) _ _ H
   obtain ⟨h,ht,hθ,hζ,hδ,hs,hl,hk,hd,hM,hg,hp⟩:=hh.gates; unfold μ' at *
   have hU' := Exponent.earns Ξ N' hB hX hI hh.gates
   have hc : (Γ).earn+δ+δ ≤ (h₀).exp := by linarith only [(Γ).worth,(Γ).second]
   refine ⟨C',d,v,w,A₀,a,r,B,q,K,x,w',t,θ,i,N',hU', medals N' hB hX hh.gates hc (half_pos (Γ).first) hh.overruns,?_,N'.position,?_,N'.income,N'.near⟩
   · intro j hj; rw [Push.PriceCompiler.beta_eq A.B.valid]
     apply (H' j hj).trans; exact Real.rpow_le_rpow_of_exponent_le h (show requested j (loss j₁)≤requested j ε from by unfold requested; linarith)
   refine ⟨fun c u h=> N'.weigh.stroke c _ (h.trans N'.talent)⟩
include hH hl hb
abbrev topDeck (l:ℕ) (e:Bool): Collection.Source G (A.B.a.S.side m n):= cohort H («χ»:=χ) ι α (M:=l) (Mesh.issue H (Ξ.upgrade H l) χ) e (fun q=> if e then ¬ l+1 ≤ q else l+1 ≤ q)
lemma viaWealth (hp:Mallow.RG12.Earned (reckon Ξ) R.shape A.delay) (l:ℕ) (hy:l ≤ j₁) (ε:ℝ)(hε: loss j₁ ≤ ε) :
    let F:=cohort H («χ»:=χ) ι α (M:=l) (Mesh.issue H (Ξ.upgrade H l) χ)
    let x:= topDeck Ξ R H l true
    let y:= topDeck Ξ R H l false
    (C!).logRead=x.logRead+y.logRead ∧ (C!).hardRead=x.hardRead ∧ (C!).hardRead=y.hardRead ∧
      (Tx).push u.beta u.eval=coarse H O C! ∧ coarse H O C! =coarse H O x*exponentialShare Z! b y ∧
      Collection.Local Z! b C! Ef Wg ∧ Collection.Local Z! b x (Ef+xF^requested (l+1) ε) Wg ∧
      ∀ t (i:ℕ), i≤l+1 → (∀ j,t j→i≤j)→ Collection.Local Z! b (F false t) (xF^requested i ε) Wg :=by
    intro F x y; obtain ⟨C',d,v,w,A₀,a,r,B,q,u₀,g,w',t,θ,i,N',D⟩:=polity Ξ R H hm hp l hy ε hε
    have h₀' : preExponent b ≤ (Γ).earn:= by unfold preExponent; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)|>.1)
    let Δ:= RG01.Survive.readerCost (G:=G) b order σ t δ β w' (1/2)
    have hx:=grounded R H O hH hm hl hb
    have hy:= YM.LocalTaylorR2.survival H D.probed ι α b rfl rfl le_rfl σ le_rfl q D.prices.1 D.launch D.prices.2 D.nonzero h₀' (half_pos (Γ).first) D.buoy l le_rfl hx (A.B.kin.path N m) (A.B.a.params m).clip u.beta (Song.weighty H χ O) α
    obtain ⟨hX,ha,hb,hY,hE,hZ⟩:=hy
    refine ⟨?_,rfl,rfl,pressure R H O hH hm N',?_,hx,?_,?_⟩
    · simpa only [y,x,topDeck,decide_true,Bool.false_eq_true,ite_false,ite_true] using! hX
    · simpa only [y,x,topDeck,Bool.false_eq_true,ite_false,ite_true] using! hZ
    · have hg:= fullLocal hE (add_le_add_right (D.charges _ le_rfl) Ef) le_rfl
      simpa only [x,topDeck,ite_true] using! hg
    intro q' k hK ht; exact fullLocal (YM.LocalTaylorR2.secondBook H D.probed ι α b rfl rfl le_rfl σ le_rfl q D.prices.1 D.launch D.prices.2 D.nonzero h₀' (half_pos (Γ).first) D.buoy _ k ht hx) (D.charges _ hK) le_rfl
end YM.LocalTaylorR2.Exponent
