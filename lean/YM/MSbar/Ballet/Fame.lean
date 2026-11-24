import YM.MSbar.Ballet.Sun
import YM.MSbar.Fiber.Frost
import YM.MergeProof.Almandine

/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
-- Can use for other payments. order pressure. Extant reading‐Z every point, Tied Stories mongoose.Beta.
set_option quotPrecheck false
variable {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}
variable (b:Bandage X C K)(Q:ℕ→ℕ)(T:Bolt A)(t:ℕ→ℕ)(Y:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail T) N p)
    (D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m))(hx:Chateau b Q T t Y D)
variable (W:YM.MSbar.Heath.Voice G)
variable (N p m:ℕ)(hm:m<N)(hG:G.Simple)
local notation "R"=> (Issue.trail T).rep N p
local notation "L"=> A.B.a.clock
local notation "H"=> Issue.trail T
open Extra.Iteration
lemma heightT (m n:ℕ)(he:n=m+1) : YM.MSbar.Heath.Stock.tip G (A.B.a.S.block m) (A.B.a.clock.hatBeta m) = (A.B.a.clock.hatBeta n):=by rw [he,block_beta]; -- namespace Extra.Iteration
variable (hX:∀ m',A.B.a.clock.hatBeta (m'+1) ≤ 2*A.B.a.clock.hatBeta m')
include hx hm
lemma households :∀ j:ℕ, WilsonStartup.Decent (A.B.a.params j).clip (A.B.a.budget j):=by
    intro s; obtain ⟨l,v,Q,U,x,he,hx,hψ⟩:=hx.motion (s+1) s 0 (Nat.lt_succ_self _) -- rfl may fail .motion
    exact ((X.machine.passes (Nat.lt_succ_self s) U.knows).1.decent)
omit hm
include hx
lemma townsR: YM.MSbar.Alto.Merit A.B.a A.B.M:=by
    obtain ⟨h,C,P₁,hM,H₀,Bf,hB,hD,hH⟩:=hx.reception -- ext flags.D
    have he:Bf.world=A.B.M:=eq_of_heq hB
    refine ⟨?_,fun n m h p=> X.pledging.conducts.full n m _ h⟩
    exact Bf.sized
-- Winter by sources inSpring
variable (hz: ∀ m:ℕ,let a:=A.B.a.clock; let i:=a.J (m+1);let j:=a.J m; let s:=a.hatBeta m; let R₀:=X.target i j; let p':= P.L i
                   (R₀.goal p' s)⁻¹*Real.exp (-(R₀.mark p' (X.shape.μ i j) s))≤ YM.MSbar.Heath.Stock.courage G p' s)
include hm hX hz hG
lemma auditorium : let Q:=A.B.a.clock.op m p; let a:=A.B.a.clock.hatBeta m; YM.MSbar.Heath.Stock.Season W (A.B.a.params m) (A.B.a.params (m+1)) a (R (m+1)) (R m) Q (YM.MSbar.Heath.Stock.courage G Q.patch.L a) :=by
   intro Q' a
   have hV:(H).Selected:=T.choice; let n:=m+1; let V:=R m; have hr:=townsR b Q T t Y D hx; have hL:= households b Q T t Y D hx N m hm; have ht:= YM.MSbar.Ballet.validP H hV hr.towns N p n hm
   have hp : Q'.patch.L= P.L (A.B.a.clock.J n):=Extra.Iteration.block_eq A.B.valid _; have hσ:=heightT m n (A:=A) rfl
   have hs:V.p.threshold=(L).threshold m:=by rw [show V.p=A.B.a.budget m from hV.represents _ _ _ hm.le|>.vac]; rfl -- notation Parser L.
   refine ⟨ YM.MSbar.Ballet.fact H hV N p m hm.le (hL _),hσ.symm ▸ YM.MSbar.Ballet.fact H hV N p n hm (hL _),(hV.steps _ _ _ hm).1,hr.towns ..,?_,ht.2,ht.1.pos,wise _ (hx.nest.samples hG N (m+1) p hm), ?_⟩
   · have he:= Bandage.inSpring b T hm hx.nest (hx.motion N m p hm)
     change YM.MSbar.Bulk.Psalm _ _ V.p.threshold _; rw [hs]; intro M i hi W hv; apply (he M i hi W hv).trans; rw [hp]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hz m) ?_) ?_
     · exact M.profit.trans ((R (m+1)).p.loMass _ _ M.profit) -- inspect
     change 0 ≤ ((H).levels.clock.op m p).push ((H).β N p (m+1)) (R (m+1)).eval W; rw [← (hV.steps N p m hm).1]; exact (YM.MSbar.Ballet.validP H hV hr.towns N p m hm.le).1.pos _|>.le
   change YM.MSbar.Heath.Quasi _ (YM.MSbar.Heath.Stock.tip G (A.B.a.S.block m) ((L).hatBeta m)*_); rw [hσ]; exact YM.MSbar.Ballet.slope H hV hr.towns N p n hm hX
end YM.PhysicalNext.Repeat.Legato
