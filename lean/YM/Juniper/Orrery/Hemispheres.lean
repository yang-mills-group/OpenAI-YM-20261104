import YM.Juniper.Orrery.Pantry
/-!
 # Export under OrbitPrice branch & Core

 Actual integration x-choice may differ from the accepted representation. At every
 subsequent step it's itself a valid input with margin, same scalar accounting
 (`reads`; VALUE of scalar kept inside, NOT claiming p scalar same after thermal
 re-presentation), safe β at exactly pinned number. Use Bank h contribution
 as analytic estimates in LOCAL ERROR contract. This theorem is the stronger
 case quantitative carry. P still on one Nursery. No changing K in this
 vacuum contraction. If mark transport on reclosed representation not used,
 need make a **physical** estimate for marks & normalization where output
 readout consumes this version. Can't leave in mark sector noncomm costs.
 Still pursuing report branch. `Bank` real. Phi is normalized Markov exactly,
 not chart circumference diameter q argument.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Org Pane Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost Guild Tabernacle Spire
open Poll Pond Blaze Gauze Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {N m n r:ℕ}
variable (U: Nursery G hG)
local notation "S"=> U.S
local notation "A"=> U.A
local notation "H"=> U.A.B.a
local notation "F₀"=> U.family
local notation "F"=> U.family.path.rep N n
local notation "L"=> U.A.B.a.clock
local notation "T"=> ((U.S).fits N n)
local notation "R"=> U.X
local notation "K"=> (F (m+1)|>.beta)
local notation "G*"=> (F m|>.beta)
local notation "V"=> U.A.B.a.S.side m n
local notation "V₀"=> U.A.B.a.S.side (m+1) n
local notation "Z"=> (L).hatBeta m
local notation "Z₀"=> (L).hatBeta (m+1)
local notation "Y"=> (L).allowance m
local notation "P"=> U.A.B.a.params m
local notation "S₀"=> (L).op m n
local notation "Ψ"=> U.A.B.a.budget m
local notation "B"=> U.A.B.a.budget (m+1)
local notation "Δ"=> (U.A.B.kin.alpha N m)
local notation "J"=> (L).J (m+1)
local notation "I"=> (L).J m
local notation "ε"=> U.S.grove.witness
local notation "w"=> (warmth H r m)
local notation "w!"=> (warmth H r (m+1))
local notation "W"=> mount U.X N m n
local notation "K*"=> Year H r
local notation "β!"=> U.A.B.a.S.side N n
local notation "Z*"=> (F N|>.beta)
open Pert.Asymptotics
variable {E:Extras G} {V':Snip G}(h:Stock (Orrery.agenda V' E) U)
        (M:∀ i:ℕ,Specs U.A i)
local notation "Y*"=> trove U h M (N:=N) (n:=n) (r:=r)
-- Reader producer can SELECT Station here and use at each step. Need legality of every kernel from Nursery family.
local notation "L₁"=> ((2:ℝ)^r)
local notation "ζ"=> Pert.Asymptotics.regulatorRun F₀ N n
local notation "x₀"=> (ζ m)^(2*r)
-- bundle path option with Step push identity. No assertion that repr x'=Orrery's choice vs independent layout or equals Spire. Empty positions don't choose unneeded below cutoff. Dependency actual path sermon.
structure Transfer : Prop where
    premiums (i:ℕ)(hi:m≤ i)(hv:i<N): |(F i).beta-(F (i+1)).beta-detects U (N:=N) (n:=n) M i| ≤ ((2:ℝ)^r*Pluto U)*(regulatorRun U.family N n i)^(2*r)
    portraits : ∃ d:∀ i:ℕ,Cham U.A.B.a i n,∃ x y: ∀ i:ℕ,Valve i n U.A.B.a (d i),∃ f:ℕ→ℝ, ∀ i:ℕ,m ≤ i → i≤ N →  Standing U N i n r (trove U (N:=N) (n:=n) (r:=r) h M i) (d i) (x i) (y i) (f i) ∧ (Tabernacle.floor (U.A.B.a.budget i) ((x i-y i).val)).EBound (U.A.B.a.budget i) (((rim/4)*((2:ℝ)^r)*(regulatorRun U.family N n i)^(2*r))*(L).allowance i) ∧ (∀ (_:i<N), (mount U.X N i n (x i).val ((U.family.path.rep N n i).beta) (f i)).eval=(U.A.B.a.clock.op i n).push ((U.family.path.rep N n (i+1)).beta) ((Dales.mount U.X N (i+1) n (x (i+1)).val ((U.family.path.rep N n (i+1)).beta) (f (i+1))).eval)) ∧ (i=N → F i=mount R N i n (x i).val ((F i).beta) (f i))
include h
lemma handle (hp:Rumbling U (n:=n) r m)(hh: Bank U h M r m N n): Transfer (m:=m) (n:=n) (N:=N) (r:=r) U h M:= by
    let C:= F₀; let W' i:= (T).W i; have hr i (hi:m ≤ i) (hv:i≤ N):= Orrery.integrate U h M hp hh i hi hv
    refine ⟨fun i hi hv=>?_,?_⟩
    · have hp:= (hr i hi hv.le).1 hv; apply hp.trans; refine (mul_le_mul_of_nonneg_left (heat_to U hv.le) ?_).trans_eq (by ring); unfold Pluto rim; have hv:= pricing (m:=m) U|>.2.2; linarith only [hv]
    have ht (i:ℕ):∃ d:Cham H i n, ∃ x y:Valve i n H d,∃ f:ℝ, m ≤ i∧i≤ N → Standing U N i n r (Y* i) d x y f∧ (i=N→ F i= mount R N i n x.val ((F i).beta) f):= by
       by_cases hz:m≤ i ∧ i≤ N; swap; · exact ⟨W' i,0,0,0,fun he=> (hz he).elim⟩
       by_cases he:i=N; · subst i; obtain ⟨x,v,u,hv,hw⟩:= embark (n:=n) (r:=r) (N:=N) U; rw [show Y* N=_ from dawn U h M]; exact ⟨x,v,v,u,fun _=>⟨hv,fun _=> hw⟩⟩
       obtain ⟨d',x,y,f,h⟩:= (hr i hz.1 hz.2).2; exact ⟨d',x,y,f,fun _=>⟨h,fun hv=> (he hv).elim⟩⟩
    choose d x y f H' using ht; refine ⟨d,x,y,f,?_⟩; intro i hi hv; obtain ⟨hK,hU⟩:= H' i ⟨hi,hv⟩; refine ⟨hK,budgetPrice U hv hK,?_,hU⟩; intro hh
    rw [hK.reads.1,(H' (i+1) ⟨hi.trans (Nat.le_succ _),hh⟩ |>.1).reads.1]; exact Cinch.pristine R hG hh U.S 0 (Spire.Uses.centerP _) (n:=n) |>.2.2.symm
omit h
include U hG
lemma advance (r:ℕ): ∀ᶠ m in atTop,∀ n:ℕ, Rumbling U (n:=n) r m:= by
   have he:=Cinch.kettle U.family hG; obtain ⟨a,ha⟩:=eventually_atTop.mp he
   filter_upwards [(H).fits.deep.eventually_ge_atTop (powerUp r),eventually_ge_atTop a] with m hm hu n
   intro i hx; exact ⟨ha _ (hu.trans hx) n,hm.trans ((H).fits.mono (by omega))⟩
include h
lemma compass (r:ℕ): ∀ᶠ m in atTop, ∀ N n:ℕ,∀ P':∀ i:ℕ, Specs U.A i, Bank U h P' r m N n → Transfer (m:=m) (n:=n) (N:=N) (r:=r) U h P':= by filter_upwards [advance U r] with m hu N n M hB; exact handle U h M (hu n) hB
end YM.Juniper.Orrery
