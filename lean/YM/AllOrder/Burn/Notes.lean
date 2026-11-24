import YM.AllOrder.Burn.Torch
import YM.AllOrder.Till.Glace
/-!
# Activation permission for an honest higher-cost E mark. Budget BEFORE any split inside the tube.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat ConnectedActivityE6 Blaze Height Raw
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented Till Floe
open AnalyticBridge VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {δ a b C ε t:ℝ}
-- p=k(logical count); bill witness.Event.
abbrev extraN (k:ℕ):ℕ:=4*k+1
abbrev alt (k:ℕ):= extraN k+3
abbrev horizon (k:ℕ):= 3*k -- lvl level actual order+2.
def credit (k:ℕ):ℝ:= -(3/8:ℝ)*alt k+1/80
def young (z:ℝ)(k:ℕ):= z^(credit k)
lemma sale_eq(k:ℕ) : credit k=-(horizon k+3:ℝ)/2+1/80:= by unfold credit horizon alt extraN; push_cast; ring
lemma amplify (k:ℕ)(G:Gauge)(L:Side) : Rate G L (credit k+ 3/8*extraN k) (fun x=> grow G L x ^ extraN k *young (betaF G x L) k):= (Rate.mul ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow (extraN k)) Rate.power).weaken (add_comm ..).le
structure PostFuel (x:ℝ)(k:ℕ)(A:ℝ):Prop where
    admits : A+x^(3/8*extraN k:ℝ)*young x k ≤ (Real.sqrt x)⁻¹ ^ (11/5:ℝ)
-- options: `C labels + perη sup` choose b.finance and permits. Split into two E classes plus quote ν.Ne.Mode.Fairness in Point.Native.
def typeT (M:Set ℕ)(k i:ℕ):ℕ:= if i∈M then 0 else extraN k
set_option quotPrecheck false
local notation "v₁"=> fun (R:Rep G f) i=> R.activities.reg i|>.site
local notation "p₁"=> fun (R:Rep G f) i=> R.activities.reg i|>.support
local notation "E"=> fun(R:Rep G f) i=> R.activities.E i
abbrev wallet (p:BudgetPoint)(R:Activities G f) (f:ℕ→ℝ)(x:Site _):=(fun i:ℕ=> if (R.reg i).site=x then p.mass (R.reg i).support (f i) else 0) -- f shadow, unknown binder Side
structure Candor (p:BudgetPoint)(R:Activities G f)(M:Set ℕ)(C δ:ℝ) : Prop where
    sale : ∃ v:ℕ→ℝ, (∀ i, p.supBounds (R.reg i|>.site) (R.reg i|>.support) (R.E i) (v i)) ∧ (∀ o:Site f, SumBudget (fun i=> if i∈M then wallet p R v o i else 0) C ∧ SumBudget (fun i=>if i∈M then 0 else wallet p R v o i) δ)
    town : ∀ (s:Signed)(b:Site f),∃ Y: R.Moves s b,∀ i, Y.ep i∈M↔ i∈M
variable {M:Set ℕ}{R:Rep G f}
lemma Candor.loosen (h:Candor R.p R.activities M C δ) (ha:C≤a)(hb:δ≤b): Candor R.p R.activities M a b:= by obtain ⟨⟨v,hV,h𝒞⟩,hp⟩:=h; exact ⟨⟨v,hV,fun x=> ⟨budget_loosen (h𝒞 x|>.1) ha,budget_loosen (h𝒞 x|>.2) hb⟩⟩,hp⟩
lemma Candor.vet (h:Candor R.p R.activities M C δ): R.activities.EBound R.p (C+δ):= by obtain ⟨f,h,hS⟩:= h.sale; refine ⟨f,h,fun i=>?_⟩; have he(p:ℕ): wallet R.p R.activities f i p=(if p∈M then wallet R.p R.activities f i p else 0)+(if p∈M then 0 else wallet R.p R.activities f i p):= (by split<;> simp); change SumBudget (wallet R.p R.activities f i) _; rw [funext he]; exact budget_plus (hS i|>.1) (hS i|>.2)
private lemma license (h:Candor R.p R.activities M C δ) (ha:R.activities.Valid R.p a b) (k:ℕ)(he:0≤t): (Raw.active t (typeT M k) R).activities.Valid R.p (C+t^(extraN k)*δ) b:= by
 obtain ⟨v,H,hv⟩:=h.sale; let g i:=t^typeT M k i; have hp i: 0≤ g i:= pow_nonneg he _; let v' i:=g i*v i; let p:=R.p; let T:= R.activities; let A:=active t (typeT M k) R; have hf i : Fairness R.p (v₁ R i) (p₁ R i) (A.activities.E i) (v' i):= by
   have hP : Fairness p (v₁ R i) (p₁ R i) (R.activities.E i) (v i):= ⟨ha.regular.smooth i, H i, ha.regular.at_flat i, fun ht f=> ha.regular.vanish i ht _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩)⟩
   unfold v'; rw (occs:=.pos [1]) [← abs_of_nonneg (hp i)]; exact hP.scale _
 refine ⟨⟨fun i=> (hf i).ready,fun i=> (hf i).one,fun i hi=> (hf i).nth hi⟩,⟨ha.forced.sym,ha.forced.symtest,ha.forced.meas,ha.forced.meas_test,ha.forced.reads,ha.forced.reads_test,ha.forced.permit⟩, fun s b=> ?_, ⟨v',fun i=>(hf i).cap,?_⟩, ha.boundK ⟩
 · obtain ⟨Y,hY⟩:= h.town s b; refine ⟨⟨Y.ep,Y.kp,Y.reg_site,Y.reg_support,Y.forced_support,Y.forced_inventory,Y.forced_tests,fun i U=>?_,Y.valuesK⟩⟩; change g (Y.ep i)*E R (Y.ep i) U= g i*E R i _; rw [show g _ = _ from (show g (Y.ep i)=g i from (by unfold g typeT; simp [hY i]))]; exact congr_arg _ (Y.valuesE i U)
 intro x; let T':=wallet p T v x; let f i:= if i∈M then T' i else 0; let h i:= if i∈ M then 0 else T' i; let F i:=f i+t^extraN k * h i; have H: wallet p T v' x=F:= by
     ext i; unfold F wallet v' f g h T' typeT; unfold wallet BudgetPoint.mass; split_ifs <;> simp [mul_left_comm]
 change SumBudget (wallet p T v' x) _; rw [H]; exact budget_plus (hv x|>.1) (budget_scale (pow_nonneg he _) (hv x|>.2))
lemma stock {S:StepData c f}{T:Tube G S}{P:Teller G}(k:ℕ)(hp:Intake P T t R)(h:Candor R.p R.activities M C (young (betaF G t S.patch.L) k))(he:PostFuel (betaF G t S.patch.L) k C):Raw.Productive (typeT M k) P T t R:= by
 have hh: 0≤ betaF G t S.patch.L:= zero_le_one.trans hp.height.le
 have hx:= license h hp.cap.labels k (t:=grow G S.patch.L t) (Real.rpow_nonneg hh _); have hu:= he.admits; let x:=betaF G t S.patch.L; rw [Real.rpow_mul_natCast hh] at hu; exact ⟨hp.ready,⟨hp.received.path,hp.received.clip,hp.received.temp⟩,⟨hp.cap.paths, { hx with boundE:=VerifiedReset.Time.E_rises hx.boundE hu }⟩,hp.exponent,hp.height,hp.sizes,hp.window⟩ -- names
end YM.AllOrder.Burn
