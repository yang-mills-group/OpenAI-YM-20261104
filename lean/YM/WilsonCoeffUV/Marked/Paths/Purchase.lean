import YM.WilsonCoeffUV.Marked.Paths.Height
import YM.WilsonCoeffUV.Marked.Capture.Geometry
/-!
# Schedule stamps for all introduced root outputs. Pay BEFORE buying nonlinear log hulls.
 Auxiliary extra pre/post prices must be composed together. Numbers on BULK Realm:
 passport allows source-a on the same A geometry.
 -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
-- outside Mer.Rolls qualified
namespace YM.WilsonCoeffUV.Wheel.Cadenza
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Supply Ticket Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c f:Side}{ι U:Type}{J I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l B':ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}{K:KernelChoices}
-- default stage side

def pulseV (G:Gauge)(e k b:ℕ)(s:ℝ)(p:0<s):=(Mer.Rolls.rootBill G b k e p).choose
def pulseZ (G:Gauge)(e k b:ℕ)(s:ℝ)(p:0<s):=(Mer.Rolls.rootBill G b k e p).choose_spec.choose

def stow (G:Gauge)(k b e:ℕ)(I:Gear G):ℝ:=let x:=min 1 I.σ
                                           let p:0<x:=lt_min zero_lt_one I.price
                                           max (pulseV G e k b x p)⁻¹ (pulseZ G e k b x p)
abbrev VestS (b k:ℕ)(R:Realm G (e+1) E)(m)(p:R.anchor≤m):= pulseV G (e+1) k b (Vσ R m p) (perk p)
abbrev VestZ (b k:ℕ)(R:Realm G (e+1) E)(m)(p:R.anchor≤m):= pulseZ G (e+1) k b (Vσ R m p) (perk p)
structure Insure (b k:ℕ)(R:Realm G (e+1) E)(W:Credit): Prop where
    proof m (h:R.anchor≤m): Mer.Rolls.Stigmata G b k (e+1) (Vσ R m h) (VestS b k R m h) (VestZ b k R m h)
    labor m (h:R.anchor ≤ m): (VestS b k R m h)⁻¹ ≤ R.cash W m ∧ VestZ b k R m h ≤ R.cash W m
lemma insured (b k:ℕ)(R:Realm G (e+1) E)(h:∀ j (v:R.anchor ≤ j), stow G k b (e+1) (R.mint j v).gear ≤ R.cash W j): Insure b k R W:=by
    refine ⟨fun j v=>(Mer.Rolls.rootBill G b k (e+1) (perk v)).choose_spec.choose_spec,?_⟩; intro j v
    exact max_le_iff.mp (h j v)
open Wheel.Address
variable {R:Realm G (e+1) E}{Ñ:ChartRatio G}{A:Levels G}{P:Sheet G}{F' D':ℕ→ℕ}{Y:Supply.Rolls P}{Ω:Protection Y}{V:Delays Ω}{o:Bar V}{b':Supply.Wait o}
lemma punchWorth (T:Finset ι)(o:ι)[DecidableEq ι](b k:ℕ)(W:Credit)(p:Insure b k R W)(v:R.anchor≤m) : let n:= Fintype.card (T.erase o); Mer.Rolls.sprigs T o (Vσ R m v) ≤ R.cash ((billingQ Unit n 0).usingC ((pur 2).prodC W)) m :=by
    intro n; unfold Mer.Rolls.sprigs; rw [show tiePay Unit 0 (Vσ R m v/8)=1 from pow_zero _,mul_one]; have ht:= p.proof m v
    have he:= ht.affordable; let C:= R.cash W m; have hx:1≤C:= Credit.purchase _ (R.depth m v); have hu:2*C≥1:=by linarith
    have h: (Vσ R m v)⁻¹ ≤ C:= le_trans (inv_anti₀ he ht.le_one) (p.labor m v).1
    apply le_trans (snuff (α:=Unit) (r:=n) (perk v) h); apply (offer_expands hu).trans; rw [cash,Credit.stock_up,Credit.products]; apply Credit.elder; exact hu; exact mul_le_mul_of_nonneg_right (pure_goal ..) (zero_le_one.trans hx)

variable [Fintype ι][DecidableEq ι]

def censusV (G:Gauge)(D k:ι→ℕ)(b t e:ℕ)(I:Gear G):= max (tellerR G D k e I) (stow G t b (e+1) I)
lemma rootedFull (pL:Paid b' A)(i:ℕ)(u:∀ i'≥ i, 5≤A.clock.J (i'+1)∧ e+1 ≤ F' (A.clock.J (i'+1)))(zL:preBoard P F' ≤ P.floorL)(vL:coolTax F' P Y Ñ (fun _=> censusV G D k b h e) ≤ V.betaEntry)(g:G.Simple)(q:LocalRatio Ñ)(sL:floors G P.kernel F'≤ P.floorL)(z:Ticket.voucher Y F' Ñ ≤ V.betaEntry):
   ∃ R:Realm G (e+1) Credit.leanC, Cloze D k R Credit.leanC∧Insure b h R Credit.leanC∧ R.draws=A∧R.paid=Ñ∧R.y=zz A∧R.anchor=i ∧ ∀ j (hb:i≤j) (t:R.anchor≤ j), (R.mint j t).σ=crestM A j (u j hb).1:=by
    obtain ⟨M,hM⟩:= Venice pL i u _ zL vL; obtain ⟨hP,hS,_⟩:= install_awards g q sL pL z _ _ u
    let R:Realm G (e+1) Credit.leanC:= ⟨A,Ñ,g,q,i, zz A,hP,hS,M.mass,M.overlap, fun i v=> by rw [Credit.lean_cost]; exact M.takes i v⟩
    have ht j (p:R.anchor≤ j): max (tellerR G D k e (R.mint j p).gear) (stow G h b (e+1) (R.mint j p).gear) ≤ R.cash Credit.leanC j:=by rw [cash,Credit.lean_cost]; exact (hM j p).1
    have hu:= fun j p=> max_le_iff.mp ((max_le_iff.mp (ht j p)).1: max _ _ ≤ _)
    exact ⟨R,⟨fun j p=>(hu j p).1,fun j p=>(hu j p).2⟩, insured b h R (fun j p=> (max_le_iff.mp (ht j p)).2), rfl,rfl,rfl,rfl, fun j _ p=>(hM j p).2⟩

-- monarchy enrollment
abbrev spac (G:Gauge)(D k:ι→ℕ)(b h e:ℕ): ℕ → Gear G→ℝ:= fun _=>censusV G D k b h e
-- imprecise spac not relevant outside COOL
lemma payout (H:Hol G)(M:Master H)(u:∀ i,k i<D i)(g:G.Simple)(q:LocalRatio Ñ)(pL:floors G P.kernel F'≤ P.floorL)(zL:(fun i=>sharp H M P.kernel Ñ i (F' i) (D' i)) ≤ P.floorL)(w: preBoard P F'≤ P.floorL)(a:Paid b' A)(hp:Ticket.voucher Y F' Ñ ≤ V.betaEntry)(hz:(fun j=>tickZ H M P.kernel Ñ (Y.L j) (F' j) (D' j) j)≤ V.betaEntry)(v: coolTax F' P Y Ñ (spac G D k b h e)≤ V.betaEntry) (c':∀ j≥i, let x:= A.clock.J (j+1); 5≤x ∧ e+1≤ F' x ∧ ∀ s:ι,k s+1 ≤ x-2 ∧ D s ≤ D' x):
    ∃ T:Realm G (e+1) Credit.leanC, T.draws=A∧T.paid=Ñ ∧ T.y=zz A∧ T.anchor=i∧ Cloze D k T Credit.leanC ∧ Insure b h T Credit.leanC ∧ Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H M k D u)) ∧∀ j (p:i≤ j) (g:T.anchor≤ j), (T.mint j g).σ=crestM A j (c' j p).1:=by
    obtain ⟨T,hT,K,he,hb,hu,ht,hv⟩:=rootedFull a i (fun j v=>⟨(c' j v).1,(c' j v).2.1⟩) w v g q pL hp
    refine ⟨T,he,hb,hu,ht,hT,K,⟨fun s=>?_⟩,hv⟩; apply Classical.choice
    obtain ⟨Y,hM,x,y,f,c⟩:= fixtures_paid H M g q pL zL a hp hz (u s) e i (fun j v=> ⟨(c' j v).1,((c' j v).2.2 s).1,(c' j v).2.1,((c' j v).2.2 s).2⟩)
    let L:= T.anchor
    let P: PassportC H T (counter H M k D u s) Credit.leanC Credit.leanC := ⟨Y,hM.trans he.symm,x.trans hb.symm,y.trans hu.symm,f.trans ht.symm⟩
    refine ⟨P, fun j a=>?_⟩
    let h:= (P.tap.symm ▸ a : P.f.arch.V.anchor ≤ j)
    obtain ⟨z,b,s,w,H'⟩:= c j h; rw [hv j (ht ▸ a), show P.f.arch.angle j h=_ from H']; exact le_rfl
end YM.WilsonCoeffUV.Wheel.Cadenza
