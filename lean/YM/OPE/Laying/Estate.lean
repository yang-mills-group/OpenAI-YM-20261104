import YM.OPE.Laying.Course
/-!
# Inventory on the actual layout

Keep a single same-order budget throughout a regulator run. The resulting
pose and stake refer to the Wilson paths at native J (all support tests on
Interior at cutoff, the actual expectation). Thaw through a signed-root
leg if needed at this fixed J; no expanding it after using the coefficient
readouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d :ℕ}{w x y :ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "F"=> C.localSection d
local notation "A"=> C.path.rep N p
local notation "B"=> Site (C.side b p)
-- tilt a stand at fixed elementary side.C.B... every epoch starts there (often consumes from q later)
def standC (C:Family G)(b N p:ℕ) : Playout C.path p b N (Site (C.side b p)):=
    ⟨Mix.camp C p b,0,hands C p b,P_on C b p, fun i he _=> Ribbons.zeroMama C b p i he, Ribbons.uphill C b b p N le_rfl⟩
local notation "E"=> standC C b N p
variable {P:Playout C.path p b N V}{K:Coefficient (C.labels.level d) (C.side i p)}
    {X:I→Cup (C.path.rep N p i)} {v:I→ℝ} {W':I→ Config G (C.side N p)→ℂ}
    {t:Cup (C.path.rep N p i)}
lemma Trial.all (L:Type)[Fintype L][DecidableEq L]: Trial (Ward.all (Names V L)):= fun _ _=>Iff.rfl
-- replace
include L h
lemma vaultType {K:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{y c:ℕ→ℝ} (he:C.ref d ≤ i) {hn:j ≤ N} (hq: Club C.path C.params (C.localSection d) (ζ d) (waybill (Y)) q j N p y D K c hn) -- impossible implicit fix
    {x:Site (C.side i p)} (hp: Studio.Mantle C.path N p i F (1,false) x (K i) t)
    (hi:q ≤ i)(hv:i ≤ j)(hw:0 ≤ y i) (u:V×Unit) (v: Playout C.path p b N V) (g:Config G (C.side i p)): y i*‖v.cupsReg i (fun _:Unit=>t) u g‖ ≤ 2 ∧ ∑ j,y i* ‖v.cupsRes i (fun _:Unit=>t) u j g‖ ≤ 1:=by
     let a:=v.tint u.1; let b:=v.positions i u.1; let w:= y i; let U:=pull a.1 b g
     rw [← Finset.mul_sum,Playout.cupsReg]; unfold stepUp; rw [norm_scalar,← Equiv.sum_comp (puff a b)]; unfold Playout.cupsRes floatUp; change w*‖t.home U‖ ≤ _∧w* (∑ j,‖stepUp a b (t.leaves ((puff a b).symm ((puff a b) j))) g‖)≤1
     simp_rw [Equiv.symm_apply_apply,stepUp,norm_scalar,hp.prose,hp.key]; exact toasted C N i p d h K (fly C.path.levels d) he (hv.trans hn) (1,false) x (hq.ticks i hi hv|>.2) hw (hq.rates i hi hv) (L.art he|>.coin i le_rfl) U

open Work
set_option maxHeartbeats 600000 in
lemma intakeLog {w c:ℕ→ℝ}{K:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}(W':Config G (C.side N p)→ℂ)(hX:Continuous W')(hj: b ≤ q)(hn:j≤N)(he: q≤ j)(hp:C.ref d ≤ q) {t:Cup (C.path.rep N p q)}{x:Site (C.side q p)}(ha:Club C.path C.params F (ζ d) (waybill (Y)) q j N p w D K c hn)(hy:Studio.Mantle C.path N p q F (1,false) x (K q) t)
    (hK:(E).Market (Ward.all (Names (Site (C.side b p)) Unit)) (fun _:Unit=>x) (fun _=>t) ((E).intention (fun _=> W') q (he.trans hn)) (fun _=> w q) (((Y).budget q).supportExponent - 3)) : (Cells.center C.S p (hj.trans (he.trans hn)) 0).rootTest (C.beta N p) W' ≤ stakes C b q/w q:=by
    let y:=b; let z:= (fun k:B×Unit=> W'); let X:=Names (Site (C.side b p)) Unit; let V':= Cells.center C.S p (hj.trans (he.trans hn)) 0
    let f:(Site (C.side b p))× Unit→ Config G (C.side N p)→ℂ:= fun k=> stepUp ((E).tint k.fst) ((E).positions N k.fst) W'; let F':= (standC C b N p).intention (fun _:Unit=>W')
    let r':= F' q (he.trans hn); let b':= (E).cupsReg q (fun _:Unit=>t); let c':=(E).cupsRes q (fun _:Unit=>t); have hy':= fun i g=> vaultType L h hp ha hy le_rfl he (hK.width ()).le i (standC C b N p) g
    obtain ⟨Fq,hq,hQ⟩:= hK.tall.grants; have he':Fq=r':=funext fun U=> (by ext i : 1; exact (hQ U i trivial).symm)
    let H':= (X); let p':H'.Mode:= ⟨Finset.univ, Finset.mem_univ _⟩; let v:= w q; have hv:0<v:= hK.width ()
    have hS := vista C.path H' N p q f (X:=F') (fun i _ hh=> (E).intention_step (fun _=> W') hh) (by unfold F' Playout.intention Playout.statute; rw [gust_base]) ((E).paidFor (fun _:Unit=>W') h.wilson (fun _=>hX) le_rfl) h.wilson (he.trans hn) p' (continuous_integrable _ (continuous_finsetProd _ fun i _=> by rw [show f i= _ from handmove C N p b (hj.trans (he.trans hn)) W' i.1]; exact (cappedC C b p N (hj.trans (he.trans hn)) (fun _=>W') (i.1,true) hX) )) (show Served (A q) b' c' r' ((E).spectrum q (fun _:Unit=>x)) (fun _=>v) _ 1 from he' ▸ hq.sold) (show Vault (fun _:B×Unit=>v) b' c' 2 1 from ⟨fun i g=>(hy' i g).1,fun i g=>(hy' i g).2⟩) (fun _=>hv) (show 0≤((Y).budget q).supportExponent-3 from by rw [show ((Y).budget q).supportExponent= _ from L.support q]; norm_num)
    let c:= (C.S.a b/C.S.a q)^4*Vac.treasury (Y) q+ (5:ℝ); let M:= Fintype.card (Site (C.side b p)); let M' := moment (C.beta N p) (fun U=>∏ i:B,V'.copy i W' U)
    unfold Tiling.rootTest; refine Stock.spacer ‖M'‖ c v M (norm_nonneg _) hv Fintype.card_pos ?_
    have hz(g): ∏ i∈ p'.val, f i g=∏ i:B,V'.copy i W' g:=by
       change (∏ i:B×Unit,_)=_; rw [Fintype.prod_prod_type]; simp; exact prod_congr rfl (fun i _=>congr_fun (handmove C N p b (hj.trans (he.trans hn)) W' i) g) -- inspect
    rw [show (fun g:Config G _=>∏ i∈p'.val, f i g)=(fun g=>∏ i:B,V'.copy i W' g) from funext hz] at hS; rw [show Poly.toll (fun _=>v) p'=v^M from by simp [Poly.toll,p',M], show (Fintype.card (Site (C.side q p)):ℝ)*Vac.treasury (Y) q+(Fintype.card (B×Unit):ℝ)*(2+1+2*1)=M*c from ?_] at hS; exact hS
    rw [Stock.tallies C.S b q p]; unfold c M; simp; ring
end YM.OPE.Log
