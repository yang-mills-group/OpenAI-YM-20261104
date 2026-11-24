import YM.Contacts.Revest.Stoke
/-! # Padded pure-epoch support. No price assumptions on Glory used here.
 Auxiliary model is ANY Score aggregated supplied. Conditions to deliver through Model/Tucks. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection Flute Outlay
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam Pressure
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{l q r v t d D' μ s:ℝ}{c f:Side} {S:StepData c f}{T:Tube G S}{k:ℕ}
namespace Pales
open Pane
variable {B:BudgetPoint} {F:bore G} (T B) (b:ℝ)
local notation "V" => virgin T B b
local notation "g" => pale f G
local notation "R" => T.up
def mold (f:Side) (G:Gauge): Pipes G f:= let u:=Pane.pale f G; ⟨u.reg,u.forced,fun i=>(u.reg i).support,fun i=> ⟨_,(u.reg i).anchor⟩⟩
def still (G:Gauge)(f:Side) : Tap G f:= ⟨0,0,0⟩
lemma canon (n:Side) {W:BudgetPoint}: Ingredients (mold n G) (still G n) W 0 0:= by -- Is K gamma=0 feasible? gamma 0 quote definition
   let X:=mold n G; let d:=still G n; have he: X.Digests d W 0 0:= by
       have h(w:Signed)(t:Site n) : ∃ f: Equiv.Perm ℕ,(∀ i,(mold n G).softer (f i)= ((mold n G).softer i).image (affine w t)) ∧ (∀ U i,d.logarithm (f i) U=d.logarithm i (pull w t U)):= let x:= ((whey n G W).moves w t).some; ⟨x.ep,x.reg_support, fun _ _=> rfl⟩ -- binder syntax
       refine ⟨whey n G W,fun i U h=> (h rfl).elim, ?_, fun _ _ _=>rfl,fun _ _ _ _ _=> rfl,fun i=>measurable_const,h⟩; refine ⟨fun _=>0,summable_zero,fun i U=>?_⟩; simp [d,still]
   refine ⟨0,0,0,he,⟨⟨le_rfl,le_rfl, by simp⟩,fun _=>0, fun _=>le_rfl,fun i U=> ?_, fun i=>?_⟩,?_⟩
   · rcases i with i|i <;> simp [Ovens.Pipes.reach,still]
   · simp [SumBudget]
   simp [Bid.quote]
variable (F k)
local notation "X" => mold f G
local notation "U" => integrated (n:=f) B F T.high R k b
def shade : Rep G f:= finish R T.high B (Flute.put X B) (Flute.lay U (still G f)) b 0
local notation "W" => shade T k F B b
-- use one-stage Reader with valid ε_σ fare. give Intake & lecturer & Toll for any charge; no coupling mismatch. Qual currently depends F H,hθ etc.
abbrev pub : Poetry.Lecturer (W) B.B:=Flute.solo ..
variable {T B F b k}
variable (ht:Salary B (integrated (n:=f) B F T.high T.up k b) s)
include ht
lemma value (x:Config G f): (W).eval x=((V)).eval x * Real.exp (- Trio.froth (U) x):=by
    unfold shade; have h:= canon (G:=G) («W»:=B) f; rw [(Flute.height ht h).unshifted, Flute.covers h, show (Progress.DirectedRecipe.trunk R T.high B (mold f G) (still G f) b 0)=(V) from rfl]; rw [sparkling]; split;
    next hx=> rw [show film B (U) x=Trio.froth (U) x from Finset.sum_congr rfl fun i _=> masked_eq _ _ _ _ (by unfold Healthy; rw [hx]; simp)]; simp [Flute.lay,still]
    simp
omit ht in
lemma glints (x: Site f) : (W).activities.E ((pub T k F B b).place x)= (U) x:= Flute.lights ..
lemma never (hs:s≤v) {d:ℝ}(hd:0≤d): (W).activities.Valid B v d∧ Toll (W) (Poetry.unknown (pub T k F B b)) v d:= by
   let z:=(W); have h:= canon (G:=G) («W»:=B) f; have hf:= Flute.height ht h; obtain ⟨a,hz,hv,hc⟩:= (trumpet R T.high B (mold f G) (still G f) U ht b 0 h)|>.wage; exact ⟨(Use.compatible_ingredients hf (by simpa only [add_zero]) hd).gates .., ⟨a,hz,fun i=> Cost.enlarge (hv i) (by linarith),fun i=>Cost.enlarge (hc i) hd⟩⟩
open Junction.Provision Junction.Provision.StagePort Junction
-- StagePort.budget already R'.p. Later Bridge Ledger.F.Price. alias here.
omit ht
lemma opening {U': Teller G} {O: ChartRatio G}{x:G.ColorIndex}{L:Side}{M:Push.Uniform.ChartPrices} {n:ℕ}(Q:StagePort G U' O x k L t v M n)(hc:Salary Q.budget (integrated (n:=Q.dew.f) Q.budget Q.importB Q.dew.T.high Q.dew.T.up k Q.dew.β) s):
    Q.flareV=(shade Q.dew.T k Q.importB Q.budget Q.dew.β).eval:= by
   funext u; rw [value hc]; apply congr_arg₂ _ rfl; apply congr_arg Real.exp; unfold StagePort.poll; rw [show Trio.froth (c:=Q.dew.f) (integrated Q.budget Q.importB Q.dew.T.high Q.dew.T.up k Q.dew.β) u = Q.dew.β * ∑ i∈Finset.range (k+1), Q.dew.grad^i * Trio.froth (Q.wook i) u from ?_]; ring
   unfold Trio.froth integrated; simp_rw [Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_; change (∑ j:Site Q.dew.f, (Q.dew.β * Q.dew.grad^i)*_)= _; rw [←Finset.mul_sum, mul_assoc]
end Pales
end YM.Contacts.Revest
