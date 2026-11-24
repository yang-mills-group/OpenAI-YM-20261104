import YM.RegulatorIR.Oracle.Calendar

/-! Supplying primitives for any such schedule. Spatial polys in meter,
no estimators about positive-degree actions or kernels at course boundaries
here. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X:Type} {M:X→ℕ} {n:Page M→Side}
namespace Circuit
variable (S:Circuit M n)
variable {K:KernelChoices}(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G) (t:Page M→Binding.Scale)
-- index transport. $S.proj$ prescription

def scroll_j (i:Page M) := crust G (S.tables Y i)
def pulses (i:Flap M) := hearth (S.pactP i) K G (S.tables Y i.prev) (S.honored Y i.prev|>.card) (Z _)
def sails (i:Flap M): Layer (Foot G) (Foot G):= projectionQ (S.pactP i) K (S.tells Y i) G

def bore (i:Flap M) : Branchix → Orders (KFoot G):=(Prim.gauss (S.rail K i) (bios _) (t i.prev) (Z (S.pactP i))).choose
lemma wheeled (i): Prim.Sphere (S.rail K i) (bios _) (t i.prev) (S.bore G Z t i):= (Prim.gauss (S.rail K i) (bios _) _ (Z (S.pactP i))).choose_spec

def opened (i:Page M):Deck (S.P i.bindW) (Foot G) (Binding.Book G (n i)):= Carto G _ _ (S.dual i) (S.comet i)

def devices (i: Flap M): GridStep (S.opened G i.prev) (S.opened G i.next):= ⟨petals (S.pulses Y G Z i),Function.swap (hoses (S.sails Y G i)),many (S.bore G Z t i)⟩

def pushP(w:Flap M):= starrier (S.pactP w) G (S.tells Y w)
def takeP(w:Flap M):= conveyer (S.pactP w) K G (S.tells Y w)

def dialect : Heir n G:= {
   P:=S.P,hp:=S.synchronize,l:=S.l,hl:=S.l_p,climb:=fun i=>by rw [S.width_s]; exact (le_mul_of_one_le_right (S.l_p _|>.le) (show (1:ℝ)≤ _ from by exact_mod_cast (S.sizeL i).property)), maps:=fun p=> S.opened G p,frames:= S.devices Y G Z t,sight:=fun i=> RegulatorIR.Gain.grain _ (S.pushP Y G i) (S.takeP Y G i) }

lemma crust_top (w:X) : S.scroll_j Y G (Page.opening M w)=finer moon :=by --replace
 let i:= Page.opening M w; let B:= S.tables Y i; have h:= (S.honored Y i); exact moon_copy G B h.card.floorP (h.top_s (by rfl)) h.card.pos.le h.card.paid h.card.stripP.2.1

-- casting no size geometry distortions. 
private lemma turnsOf {p f:Side}{P:Patch}{B B':Bed}{R: Cross P.L (TypeFace 1) (TypeFace 1)}(T:StepData p f) (hp:T.patch=P)(hz:T.kernel=K) (h:f=p*P.L) (he:Even f.val) (hn:Even p.val){t l r:ℝ}(hb:t*f.val=r)(hf:l*p.val=r) {σ σ' Ω Ω' α α' υ:ℝ}{V W:Clip}(F:Hall B σ Ω α V)(C:Hall B' σ' Ω' α' W)(H:BidP P K B B' R σ υ)(Xv:∀ n,Bid.Sworn B n G): Bedload (Carto G t r he hb) (Carto G l r hn hf) K.penalty (awake T (bios T)) (crust G B) (crust G B') (finer (fringe T)) (projectionQ P K R G) (hearth P K G B F (Z _)):=by
 subst f; have he':T=avenue P K p:=by obtain ⟨v,k,a⟩:=T; change v=P at hp;change k=K at hz;subst v;subst k;rfl
 subst T; exact worth_E P K G B B' R F C (Z _) H Xv he hb hn hf

def lane : Reel (S.dialect Y G Z t):= {
 clock:=t, steps:=S.rail K, phase:=S.comet, even:=S.dual, deep:= S.stands,realms:=fun _=>rfl,teeth:=fun p=> Z (S.pactP p),forest:=fun i=>bios (S.rail K i),landscape:=fun _=>Field.Square.proper ..,
 stem:=S.scroll_j Y G, apex:=crust_top S Y G,Dtr:=S.sails Y G,pulses:= S.pulses Y G Z
 meanF:=fun _=>rfl,bondF:=fun _=>rfl,moduli:=fun i=>turnsOf G Z (S.rail K i) rfl rfl (S.seats i) (S.dual _) (S.dual _) (S.comet _) (S.comet _) (S.honored Y i.prev).card (S.honored Y i.next).card (S.predicted Y i) (fun n=>S.honored Y i.prev|>.symmetryP n G), powers:=fun w=>⟨_,S.wheeled G Z t w,rfl⟩ }

lemma translation (e:Foot G) (x:Cover): motionsQ e x= carryX x e:= rfl
lemma passage : Passage (S.lane Y G Z t) :=by
 constructor
 · intro i x a b; have h:=placates (S.pactP i) K (S.tells Y i) G a b x; rw [strut,site_roll, translation,translation] at h; exact h
 intro i p a b; have h:=phaseT (S.pactP i) K G (S.tables Y i.prev) (S.honored Y i.prev).card (Z _) a b p; rw [strut,strut, translation,translation] at h;exact h
end Circuit
end YM.RegulatorIR.Oracle
