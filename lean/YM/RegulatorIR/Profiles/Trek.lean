import YM.RegulatorIR.Profiles.Product
import YM.RegulatorIR.Cluster.Savings
import YM.RegulatorIR.Tape.Scoria

/-!
# Kick data over finite regulator. Construction for common and cover marks

Consumers need authentication against RG08 analytic taps on independent
cover, here Milieu construction from cover lines and Pose cap, never from
all orbit costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I:Type}{u b p j k a s m e:ℕ}{M: W→ℕ}{n:Page M→Side} {L:Meter W}{J D:Choice M}
variable {S:Heir n G} (R: Reel S) {Γ: Flap M → Layer (Foot G) (Foot G)} {V: Flap M → Bride G}
  {c: Flap M→ℝ≥0∞} {T:S.Accounts}

def atopA (w:W) := many (plain_exists (R.clock (Page.opening M w)) G).choose
def nativeVac : S.Accounts := {
 bulk:= seriesC (X:=fun _=>Orders (Foot G)) (atopA R) fun w=>(S.frames w).pure
 orb:= seriesC (X:=fun p=>Orders (Book G (n p))) (fun w e r=> (S.maps (Page.opening M w)).deckSum (atopA R w e r)) (fun w=>(S.frames w).common)
 step_v:= fun f=>(laterC f).symm
 step_o:=fun f=>(laterC f).symm
 top_v:=fun w=>(Flight.grammar (ark _ (R.even (Page.opening M w)) (R.phase _) (plain_exists _ G).choose_spec))
 top_o:=fun w=>by
    rw [earlierC, R.realms]; exact (Flight.format (ark _ (R.even (Page.opening M w)) (R.phase _) (plain_exists _ G).choose_spec)) }
lemma followsVac : R.Follows (nativeVac R):= fun _=> ⟨(plain_exists _ _).choose,(plain_exists _ _).choose_spec,rfl,rfl⟩

def declaring (T:S.Accounts)(a:W→ Orders (Foot G))(h:∀ w,Ranks m (a w)): T.Report m := {
 main:= seriesC (X:=fun _=>Orders (Foot G)) a (fun w=>(S.frames w).each m (T.bulk w.prev)), point:=seriesC (X:=fun p=>Orders (Book G (n p))) (fun w e r=> (S.maps (Page.opening M w)).scroll (a w e r)) fun w=>(S.frames w).island m (T.orb w.prev)
 step_m:=fun w=> (laterC w).symm, step_p:=fun w=>(laterC w).symm
 ceilingM:=h, same:=fun _ _ _=> rfl, ceilingP:=fun w i r hi=>h w i r (fun hg=>hi (by rw [earlierC,hg]; exact Deck.scroll_zero ..)) }
section Insert
variable {m s: I→ℕ}
variable (K:Composite I)(P:I→W→Portrait G)(Z:∀ i,T.Report (m i))

def principal : T.Report (K.accounts m):= declaring T (fun w=>K.product (fun i=>(Z i).main (Page.opening M w))) (fun w=> K.ranks _ fun i _=> (Z i).ceilingM w)
def drawing (w:W):=Gather K (fun i=> P i w)
variable (Hv:∀ i,K.In i→∀ w,Halo.BasisT (m i) (s i) (P i w) ((Z i).main (Page.opening M w)))
include Hv
lemma inaugural (w):Halo.BasisT (K.accounts m) (K.accounts s) (drawing K P w) ((principal K Z).main (Page.opening M w)):= BasisT.given K (fun i=> P i w) (fun i hi=> Hv i hi w) fun i _=>(Z i).ceilingM w
lemma launches (z:I)(hq:K.In z) : ∀ i,gradedSymmetric ((Z z).main i):=by
 refine Page.proves (fun w=> (Hv z hq w).symmetry) ?_
 intro w _; rw [← (Z z).step_m]; intro i j; exact crop_symm _ _ (is_symmetry _)
end Insert
structure SchemeBeam (R:Reel S)(T:S.Accounts)(Γ:Flap M→ Layer (Foot G) (Foot G))(V:Flap M→Bride G)(L:Meter W)(c: Flap M→ ℝ≥0∞)(p k:ℕ) : Prop where
  port : R.Follows T
  price : Halo.Aug.Amenities S L p k
  inspiration : Inspires Γ V S
  rates : Azur R Γ V k L c
  bulk : S.Supplies T L p k
  mirror : ∀ w i j,R.pulses w i j=R.pulses w j i
variable {R}
namespace SchemeBeam
variable (K: SchemeBeam R T Γ V L c p k)
include K
lemma aligns : ∀ i,gradedSymmetric (T.bulk i):=by
 refine Page.proves ?_ ?_
 · intro w; obtain ⟨v,h,hv,h'⟩:= K.port w; rw [hv]; exact (ark _ (R.even _) (R.phase (Page.opening M w)) h).symm
 intro w _; rw [← T.step_v]; intro i j; unfold GridStep.pure; split; exact Diagram.symmetric_zero; exact crop_symm _ _ (is_symmetry _)
lemma milieu : Milieu S T k p L:=by
 refine ⟨K.rates.era K.inspiration p K.price, K.bulk,fun w i j=> ?_,?_⟩
 · apply Diagram.symmetric_add (offer_symm _ _ (K.aligns w.prev i j)); obtain ⟨v,hv,hp⟩:= R.powers w
   change IsSym ((S.frames w).addon i j);rw [hp]; exact (Prim.cosmos _ _ _ (R.teeth w) (R.even _) (R.phase w.prev) (R.even _) (R.phase w.next) hv).symm i j
 intro w i j; change (S.frames w).line _ _=(S.frames w).line _ _;rw [R.bondF]; cases i <;> cases j <;> first| exact K.mirror w _ _ | rfl
lemma emits (hb:0<b)(hk: quantum b u ≤ k): Cylinder R T Γ V L c p b u:= ⟨hb,K.port,K.price.enough hk,K.inspiration,K.rates.scale_down hk,Halo.Aug.T_enough T K.bulk hk⟩
end SchemeBeam
end YM.RegulatorIR.Profiles
