import YM.FormalOPE.RG10.Inherit.BrightSky
/-!
 # All expenses have a genuine local saddle calculus at every level
 of the Fabric hierarchy (before gauges or representation costs).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{f:Side}
variable (L:Fabric G f)(T : L.loom.Truss)(w: L.Accounts→ℝ)

-- top+ independent L.More noise only after peeling using true costs
 def premi (v:Booth L) (i:L.Accounts):= i.elim (Orb.account (v ∘ Sum.inl)) (L.air (v ∘ Sum.inr))
 def overall (w:L.Accounts→ℝ)(v:Booth L): ℝ:=∑ i,w i*premi L v i
lemma proven (a:L.Accounts) : Component (fun v=>premi L v a):= a.recOn (Strong.view (J:=Reference L) Sum.inl (endcap (G:=G) L.even).toComponent) fun i=> (Strong.view (J:=Reference L) Sum.inr (every_reference L i))

lemma premSplit : overall L w = Strong.united (w none • (Orb.account (G:=G) (n:=f))) (L.production (w∘some)):= by ext1 v; unfold overall; rw [Fintype.sum_option]; rfl
lemma full_stamp (hw:∀ i,0<w i) : Strong (overall L w):=by rw [premSplit]; exact Strong.merge ((endcap (G:=G) L.even).tune (hw none)) (reference L (fun i=>hw _ )) -- composition

-- bridge witnessing: for any account send from truss over genuine joint step to independent pension
 def fromJoint : Configuration G T.Bulk → Booth L := (attune L).placement ∘ (bridge L).placement ∘ (reset L.loom T L.atop).placement
lemma credential (a:Spending G (Reference L))(C:Credential a) : Credential (a ∘ fromJoint L T):= ((C.pull (attune L)).pull (bridge L)).pull (reset ..)
lemma tolerable (a:Spending G (Reference L))(C:Component a): Component (a ∘ fromJoint L T):=((C.pull (attune L)).pull (bridge L)).pull (reset ..)

lemma accurate_top (u: Configuration G L.atop.Bulk)(i:L.Accounts): L.price (L.atop.board u) i = premi L ((attune L).placement ((bridge L).placement u)) i:= by
 let a:= L.atop.board u
 let y:= (bridge L).placement u
 cases i with
 | none => change Fabric.wilson (L.principal a)= Orb.account (y∘Sum.inl); rw [←accounting,key_agrees]
 | some i=> change L.regional a i=L.air (L.dry (key L y) (y∘ Sum.inr)) i
            dsimp only [y,a]
            rw [key_agrees,terminal_agrees,←Fabric.costs,L.comb_principal]
lemma accurate (u: Configuration G T.Bulk)(i:L.Accounts): L.price (T.board u) i = premi L (fromJoint L T u) i:= by
 rw [show fromJoint L T u=(attune L).placement ((bridge L).placement (T.transfer _ u)) from rfl, ← accurate_top, Loom.Truss.transfer_spin, Loom.Truss.treeGauge, L.price_gauge]
lemma punctual (i:L.Accounts): Component (fun u=> L.price (T.board u) i):= by
 have H: (fun u=>L.price (T.board u) i)=(fun v=>premi L v i) ∘ fromJoint L T:= funext fun u=> accurate L T u i
 rw [H]; exact tolerable L T _ (proven L i)
-- ready-to-use Gram and stationarity everywhere on finite gauges (no comparable gain bound here).
lemma prepared (hw:∀ i,0<w i): Credential ((L.spend w) ∘ T.board):= by
 rw [show L.spend w ∘ T.board= overall L w ∘ fromJoint L T from funext fun x=>by unfold Fabric.spend overall; simp_rw [Function.comp_apply,accurate]]
 exact credential L T _ ((full_stamp L w hw).toCredential)
end YM.FormalOPE.RG10.Inherit
