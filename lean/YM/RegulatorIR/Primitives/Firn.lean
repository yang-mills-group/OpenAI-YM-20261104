import YM.RegulatorIR.Primitives.Mass
import YM.RegulatorIR.Primitives.Parades

/-! Translation & inversion native charts and finite supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Chart Gauge RG Orb
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I J X:Type}{k a b:ℕ}{f c:Side}{l P:ℝ} {G:Gauge}

abbrev Foot (G:Gauge):= Long G.ColorIndex

def timber (G:Gauge)(x:Foot G→ℝ)(i: Edge Cover) : G.Color:= WithLp.toLp 2 (fun j=>x (i,j))
lemma timber_0 : timber G 0=0:=rfl
lemma timbers (x:Foot G→ℝ)(s:ℝ) : timber G (s • x)=s • timber G x:=rfl
lemma timberBridge (H: Even f.val)(hr:l*f.val=P)(x:Horizon G f) : timber G (bridge (Carto G l P H hr) (paper G f x))= fire x ∘ around f:=by ext i a; exact firebrand H hr x a i

-- for infinite charts; joints

def win (G:Gauge)(x:Foot G→ℝ) : CoverConfig G:=fun i=> G.lieExp (timber G x i)
lemma win_o (H:Even f.val)(hr:l*f.val=P)(x:Horizon G f): win G (bridge (Carto G l P H hr) (paper G f x))=orbLift (climb x) ∘ around f:=by
 ext1 i; unfold win;rw [timberBridge, mat_expanded]; simp only [Function.comp_apply,Work.F03.represent_link,canvas,show ∀ i: Axis, Exterior.axisEquiv.symm (Exterior.coord i)=i from fun i=>Exterior.axisEquiv.symm_apply_apply i]
lemma pivot_dir {R:Type}[AddCommGroup R][One R](t:Four R): invS.act t= -t:=by ext i; simp [invS,Signed.act]

-- actual link read across motions
def parity : Motion→ Signed
 | across _=>1
 | turn _=> invS

def baseR (f: Side)(d: Motion): Cover:= match d with
 | across v=> f.val • v
 | turn v=> f.val • v
lemma lifted (n:Side)(d:Motion) (U:CoverConfig G)(i:Edge Cover): pull (parity d) (baseR n d) U i=match d with
 | across _=> U (court n d i)
 | turn _=> (U (court n d i))⁻¹ :=by
 cases d with
 | across v=> unfold parity; rw [pull_one]; simp [translate,court,dis,baseR,add_comm]
 | turn v=> rw [pull]; change (U (-i.1+_ - step i.2,i.2))⁻¹=_ -- need pivot first
            unfold court dis reco baseR;simp only; congr 3; abel
lemma timber_tool (H: Even f.val)(hz:l*f.val=P)(d:Motion)(i:Edge Cover)(w: Foot G→ℝ): timber G (toolP (Carto G l P H hz) d w) (court f d i)= d.sign • timber G w i:=by
 ext1 j;change d.sign*w ((Carto G l P H hz).wind d|>.symm <| (court f d i,j))= d.sign*w (i,j);exact congr_arg (fun t=>d.sign*w t) (((Carto G l P H hz).wind d).symm_apply_apply (i,j))
lemma tools_links (H:Even f.val)(hz:l*f.val=P)(d:Motion)(U:Foot G→ℝ): pull (parity d) (baseR f d) (win G (toolP (Carto G l P H hz) d U))=win G U:=by ext1 i; rw [lifted];cases d <;> simp only [win, timber_tool H hz,Motion.sign] <;> simp [Work.F03.exp_neg_color]

-- locality helper

def Names {K:Type}(T: (I→K)→X)(r:Finset I):Prop:=∀ w z,(∀ i∈r,w i=z i)→T w=T z
def steps (p:Cover) : Walk→Finset (Edge Cover)
 | []=>∅
 | a::l=>insert (a.used p) (steps (p+a.vec) l)
lemma travel_knows (p:Cover)(w:Walk) : Names (fun U:CoverConfig G=>travel U p w) (steps p w):=by
 induction w generalizing p with
 | nil=>intro _ _ _;rfl
 | cons a w ih=>intro U V he; let i:=a.used p; have hx:= he i (Finset.mem_insert_self ..); have ht:= ih (p+a.vec) U V (fun i hi=> he i (Finset.mem_insert_of_mem hi)); unfold travel; apply congr_arg₂ (· * ·) _ ht; unfold Lattice.Step.read;split <;> first|exact hx|exact congr_arg Inv.inv hx

variable {E:Type}
def placeFin (S:Finset I) : ↥S↪I:=⟨Subtype.val,Subtype.val_injective⟩
def fill (F:J↪I)(v:J→ℝ)(x:I):ℝ := dilute F v x
lemma fill_eq (S:Finset I)(i:I)(h:i∈S)(w: I→ ℝ) : fill (placeFin S) (w ∘ placeFin S) i=w i:= dilute_here _ _ (⟨i,h⟩:↥S)
def liftFill (F:J↪I) : (J→ℝ)→ₗ[ℝ](I→ℝ) where
 toFun:= fill F
 map_add' v w:=by
    ext1 x; by_cases h:x∈Set.range F
    · obtain ⟨i,rfl⟩:=h; unfold fill;simp [dilute_here]
    unfold fill; rw [Pi.add_apply,dilute_miss F _ _ h,dilute_miss F _ _ h,dilute_miss F _ _ h]; simp
 map_smul' t v:=by
    ext1 x; by_cases h:x∈Set.range F
    · obtain ⟨i,rfl⟩:=h; unfold fill;simp [dilute_here]
    unfold fill;rw [Pi.smul_apply,dilute_miss F _ _ h,dilute_miss F _ _ h]; simp

def timberL (G:Gauge)(S:J↪Foot G)(x:Edge Cover): (J→ℝ)→ₗ[ℝ] G.Color where
 toFun u:= timber G (liftFill S u) x
 map_add' v w:=by rw [map_add];rfl
 map_smul' t v:=by rw [map_smul];rfl
lemma tall (S:Finset (Foot G)) (x:Edge Cover) : ContDiff ℝ ω (fun v:↥S→ℝ=>timber G (fill (placeFin S) v) x):=(timberL G (placeFin S) x).toContinuousLinearMap.contDiff
end YM.RegulatorIR.Prim
