import YM.Integration.FVA1Physical.Round2.CircuitAnalytic

/-! The C18 physical history supplies the small-field estimate, the conditional vacuum and the complete bare input at each actual step. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
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

variable {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C:ℕ→ℝ}{K:Bid.Worth}
    {T:Bolt A} {l : ℕ} (g : Bandage.Harmonics X C K T l)
    (room : coarseRoom M P A X)
variable (W:YM.MSbar.Heath.Voice G)
variable (N p m:ℕ)(hm:m<N)(hG:G.Simple)
local notation "R"=> (Issue.trail T).rep N p
local notation "L"=> A.B.a.clock
local notation "H"=> Issue.trail T
open YM.MSbar.Midpoint YM.MSbar.Rolling
open YM.MSbar.Bakery Pressure YM.MSbar.Bakery.Portal
local notation "t!"=> A.B.a.clock.hatBeta
local notation "cue"=> YM.MSbar.Heath.Stock.cue
local notation "θ"=> YM.MSbar.Aqua.film
variable (hX:∀ m',A.B.a.clock.hatBeta (m'+1) ≤ 2*A.B.a.clock.hatBeta m')
variable (hz: ∀ m:ℕ,let a:=A.B.a.clock; let i:=a.J (m+1);let j:=a.J m; let s:=a.hatBeta m; let R₀:=X.target i j; let p':= P.L i
                   (R₀.goal p' s)⁻¹*Real.exp (-(R₀.mark p' (X.shape.μ i j) s))≤ YM.MSbar.Heath.Stock.courage G p' s)
include hm hX hz g room
lemma circuit_season : let Q:=A.B.a.clock.op m p; let a:=A.B.a.clock.hatBeta m; YM.MSbar.Heath.Stock.Season W (A.B.a.params m) (A.B.a.params (m+1)) a (R (m+1)) (R m) Q (YM.MSbar.Heath.Stock.courage G Q.patch.L a) :=by
   intro Q' a
   have hV:(H).Selected:=T.choice; let n:=m+1; let V:=R m; have hr:=circuit_merit room; have hL:= circuit_decent g; have ht:= YM.MSbar.Ballet.validP H hV hr.towns N p n hm
   have hp : Q'.patch.L= P.L (A.B.a.clock.J n):=Extra.Iteration.block_eq A.B.valid _; have hσ:=heightT m n (A:=A) rfl
   have hs:V.p.threshold=(L).threshold m:=by rw [show V.p=A.B.a.budget m from hV.represents _ _ _ hm.le|>.vac]; rfl -- notation Parser L.
   refine ⟨ YM.MSbar.Ballet.fact H hV N p m hm.le (hL _),hσ.symm ▸ YM.MSbar.Ballet.fact H hV N p n hm (hL _),(hV.steps _ _ _ hm).1,hr.towns ..,?_,ht.2,ht.1.pos,wise _ (g.samples N (m+1) p hm), ?_⟩
   · have he:= circuit_psalm g N m p hm
     change YM.MSbar.Bulk.Psalm _ _ V.p.threshold _; rw [hs]; intro M i hi W hv; apply (he M i hi W hv).trans; rw [hp]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hz m) ?_) ?_
     · exact M.profit.trans ((R (m+1)).p.loMass _ _ M.profit) -- inspect
     change 0 ≤ ((H).levels.clock.op m p).push ((H).β N p (m+1)) (R (m+1)).eval W; rw [← (hV.steps N p m hm).1]; exact (YM.MSbar.Ballet.validP H hV hr.towns N p m hm.le).1.pos _|>.le
   change YM.MSbar.Heath.Quasi _ (YM.MSbar.Heath.Stock.tip G (A.B.a.S.block m) ((L).hatBeta m)*_); rw [hσ]; exact YM.MSbar.Ballet.slope H hV hr.towns N p n hm hX

end YM.PhysicalNext.Repeat.Legato.Round2
