import YM.LocalTaylorR2.Calendar
/-!
 # Physical Shape solver, prior to prediction/re-expression.
 Earned premiums expose other derivative precision in the same calendar.
 Invoices keep noisy and hard letters. `reserve` K is actual-strong,
 not an ad-hoc power converted from the requested Taylor output order.
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
structure ReadyHere (l:ℕ) (H:Guide A.B R.shape N m n u)(ε v q e t:ℝ) (y : H.ThinP→Orders l→ℝ) (z:H.ThinP→ℝ):Prop where
    probed : ReadyAll χ (Candle.sprig H χ) v (order) y z t
    buoy : Ready H.smallAt (radiusB β) (fun i=>2^order*z i) ((Γ).earn+δ) e δ (1/2)
    charges (i:ℕ) : i ≤ l+1 → readerCost (G:=G) b order σ t δ β e (1/2) i ≤ xF^(requested i ε)
    nonzero : 0<v
    launch : Sailor G (b).threshold q order
    prices : 0≤q ∧ order*q≤v
include hm
lemma deliver (hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay) (l:ℕ)(hy:l ≤ j₁)(ε:ℝ)(hε: loss j₁ ≤ ε) :
    ∃ (C' d v w A₀ a r B q D' x w' t θ:ℝ) (i:ℕ) (N':Captain H order C' d v w A₀ a r B q (i+order) χ),
       ReadyHere R l H ε v q w' t (YM.LocalTaylorR2.Price.schemePrice N' D' x θ) (YM.LocalTaylorR2.Price.result N' θ (l+1:ℝ) t D' x l) := by
   let μ' := μ
   have hv:= H.laws.data.funds
   have hu:=hp _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) ⟨(Tx).patch,hv.funds.kernel,hv.length_eq,hv.funds.atStep⟩ l hy
   have hf := params_eq A.B.valid m
   have hh : Written h₀ L! (R.walls j₁ j₀) μ' β (loss j₁) δ (turnFee b) order σ l (R.shape.o j₁ j₀) χ := by
     change Written _ _ _ _ _ _ _ (Push.Local.turnCost (A.B.a.params m).order (A.B.a.params m).power) (A.B.a.params m).order (A.B.a.params m).power _ _ _; rw [hf]; exact hu
   obtain ⟨A₀,a,C',x,d,v,w,r,B,K,q,t,y,w',θ,i,k,hh,H'⟩:= hh
   obtain ⟨N',hB,hX⟩:=hh.chooses _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) _ _ H
   obtain ⟨h,ht,hθ,hζ,hδ,hs,hl,hk,hd,hM,hg,hp⟩:=hh.gates; unfold μ' at *
   have hU' := YM.LocalTaylorR2.Price.credentials N' hB hX h hζ ht hθ hs hl hk hδ
   have hc : (Γ).earn+δ+δ ≤ (h₀).exp := by linarith only [(Γ).worth,(Γ).second]
   refine ⟨C',d,v,w,A₀,a,r,B,q,K,x,w',t,θ,i,N',hU', YM.LocalTaylorR2.Price.secondReady N' hB hX h hζ ht hθ hd hc (half_pos (Γ).first) hM hp hg,?_,N'.position,?_,N'.income,N'.near⟩
   · intro j hj; rw [Push.PriceCompiler.beta_eq A.B.valid]
     apply (H' j hj).trans; exact Real.rpow_le_rpow_of_exponent_le h (show requested j (loss j₁)≤requested j ε from by unfold requested; linarith)
   refine ⟨fun c u h=> N'.weigh.stroke c _ (h.trans N'.talent)⟩
include hH in
lemma pressure {C' d v w A₀ a r B q:ℝ} {l:ℕ} (N':Captain H order C' d v w A₀ a r B q l χ) : (Tx).push u.beta u.eval=coarse H O C!:= by
   have h:= A.B.support.cap N m hm.le
   funext V; exact (Song.forward b H ι χ α N' O rfl le_rfl h hH V).symm

include hH hl hb
abbrev interpret (l:ℕ) (e:Bool): Collection.Source G (A.B.a.S.side m n):= cohort H («χ»:=χ) ι α (M:=l) (Candle.sprig H χ) e (fun q=> if e then ¬ l+1 ≤ q else l+1 ≤ q)
lemma transmit (hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay) (l:ℕ) (hy:l ≤ j₁) (ε:ℝ)(hε: loss j₁ ≤ ε) :
    let F:=cohort H («χ»:=χ) ι α (M:=l) (Candle.sprig H χ)
    let x:= interpret R H l true
    let y:= interpret R H l false
    (C!).logRead=x.logRead+y.logRead ∧ (C!).hardRead=x.hardRead ∧ (C!).hardRead=y.hardRead ∧
      (Tx).push u.beta u.eval=coarse H O C! ∧ coarse H O C! =coarse H O x*exponentialShare Z! b y ∧
      Collection.Local Z! b C! Ef Wg ∧ Collection.Local Z! b x (Ef+xF^requested (l+1) ε) Wg ∧
      ∀ t (i:ℕ), i≤l+1 → (∀ j,t j→i≤j)→ Collection.Local Z! b (F false t) (xF^requested i ε) Wg :=by
    intro F x y; obtain ⟨C',d,v,w,A₀,a,r,B,q,u₀,g,w',t,θ,i,N',D⟩:=deliver R H hm hp l hy ε hε
    have h₀' : preExponent b ≤ (Γ).earn:= by unfold preExponent; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact (R.pledging.agenda _ _ (step_paid A.B.a m)|>.1)
    let Δ:= RG01.Survive.readerCost (G:=G) b order σ t δ β w' (1/2)
    have hx:=grounded R H O hH hm hl hb
    have hy:= YM.LocalTaylorR2.survival H D.probed ι α b rfl rfl le_rfl σ le_rfl q D.prices.1 D.launch D.prices.2 D.nonzero h₀' (half_pos (Γ).first) D.buoy l le_rfl hx (A.B.kin.path N m) (A.B.a.params m).clip u.beta (Song.weighty H χ O) α
    obtain ⟨hX,ha,hb,hY,hE,hZ⟩:=hy
    refine ⟨?_,rfl,rfl,pressure R H O hH hm N',?_,hx,?_,?_⟩
    · simpa only [y,x,interpret,decide_true,Bool.false_eq_true,ite_false,ite_true] using! hX
    · simpa only [y,x,interpret,Bool.false_eq_true,ite_false,ite_true] using! hZ
    · have hg:= fullLocal hE (add_le_add_right (D.charges _ le_rfl) Ef) le_rfl
      simpa only [x,interpret,ite_true] using! hg
    intro q' k hK ht; exact fullLocal (YM.LocalTaylorR2.secondBook H D.probed ι α b rfl rfl le_rfl σ le_rfl q D.prices.1 D.launch D.prices.2 D.nonzero h₀' (half_pos (Γ).first) D.buoy _ k ht hx) (D.charges _ hK) le_rfl
end YM.LocalTaylorR2.CalendarStep
