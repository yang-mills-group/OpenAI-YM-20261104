import YM.RegulatorIR.Oracle.Rents

/-! precision metric S1 native-color insertion. Top curvature conversion by
actual Radial.Grid. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {X Y A : Type} {n f: Side} {r s p:ℕ} {α σ:ℝ}
-- non-G-paired scalar matrices
def colorK (G:Gauge)(H:Row (TypeFace r) (TypeFace s)) : Row (PAC G r) (PAC G s):= fun i j z=> if i.2=j.2 then H i.1 j.1 z else 0
lemma color_inst (G:Gauge)(H:Row (TypeFace r) (TypeFace s)) (n:Side): (colorK G H).acts n=tensor G (H.acts n):=by
 ext ⟨x,i,j⟩ ⟨y,k,a⟩;by_cases h:j=a
 · simp_rw [Row.acts,FreeResolvent.tensor,colorK, Matrix.of_apply,if_pos h]
 simp_rw [Row.acts,FreeResolvent.tensor,colorK, Matrix.of_apply,if_neg h];simp
lemma color_strip (G:Gauge)(H:Row (TypeFace r) (TypeFace s))(h:H.strip σ α)(hh:0≤α): (colorK G H).strip σ α:=by
 intro i j; unfold colorK; split
 next _=> exact h _ _
 simp [Laurent.Width,SumBudget,hh]

def crust (G: Gauge) (B: Precision.Bed): Layer (Long G.ColorIndex) (Long G.ColorIndex):= lading (linksQ G) (linksQ G) (colorK G (FreeResolvent.hBlock B.metric))
lemma crustA (G:Gauge)(B : Precision.Bed) : Albedo (linksQ G) (linksQ G) (crust G B):= ladingW _ _ _
lemma crust_price (G:Gauge)(B: Precision.Bed) (h:B.metric.strip σ α)(hs:0≤σ)(hm:0≤α): chestE (linksQ G) (linksQ G) σ (crust G B) ((Fintype.card (PAC G 1):ℝ≥0∞)*ENNReal.ofReal (FreeResolvent.kinPrice σ α)):=roots _ _ (color_strip G _ (FreeResolvent.hBlock_width hs h) (FreeResolvent.kinPrice_nn _ α hm))
lemma crust_id (G:Gauge)(B : Precision.Bed) (h:B.metric.strip σ α)(hs:0≤σ) (n): ledgerRow (linksQ G) (linksQ G) (crust G B) n=tensor G (Precision.K (B.metric.acts n)) :=by
 unfold crust; rw [ledger_lade,color_inst,FreeResolvent.hBlock_periods hs h]; rfl

-- Finsupp ledger using support. READ money from actual stencil on full lattice.
lemma stark {Y : Type}(k : X→₀ ℝ)(h:X→Y)(y:Y): Stalk.collect h k y= ∑ i∈ k.support, if h i=y then k i else 0:=by
 classical
 let f (i:X):=if h i=y then k i else 0
 have hh:Stalk.collect h k y=∑'i,f i:=by
    convert tsum_subtype (f:=(k:X→ℝ)) {x| h x=y} using 1 <;> rfl
 rw [hh]; exact tsum_eq_sum fun i hi=> by have ht:= Finsupp.notMem_support_iff.mp hi;unfold f;rw [ht,ite_self]
-- any field action on finite torus; recover projection from checking ALL vectors
lemma cargo_of (X:Type) {Y S I:Type} {P T : Side→Type} (W:Quarry X I P)(Z: Quarry Y S T)(x:X) (n:Side) [Fintype I][Fintype S][Fintype (T n)] (H : X→ Y →₀ ℝ)(h:Albedo W Z (finer H))(v:T n→ℝ): (ledgerRow W Z (finer H) n*ᵥ v) (W.swrap n x) = combo (v ∘ Z.swrap n) (H x):=by
 rw [transmit W Z _ _ _]
 · change (∑'i,H x i* _)=_;rw [tsum_eq_sum (s:=(H x).support)]
   · rfl
   intro i hi;rw [Finsupp.notMem_support_iff.mp hi,zero_mul]
 · -- actually Billed only with finite I; add
   exact ((FundE.bill_s h (fun i=>(H i).hasFiniteSupport) 0).buys le_rfl).1
 exact h
-- moon $K stencil translation.
lemma solar (x:Cover)(a:PlaqAxes)(i:G.ColorIndex) (d:Cover)(j:Long G.ColorIndex):sun (d+x) a i (motionsQ j d)=sun x a i j := by
 let f(u v : Long G.ColorIndex):= Finsupp.single u (1:ℝ) v
 have hp x y: f (motionsQ x d) (motionsQ y d)=f x y:=by
    rw [← site_roll,← site_roll]; unfold f; simp [Finsupp.single_apply]
 simp only [sun,Finsupp.sub_apply,Finsupp.add_apply]
 let r:= a.val.1;let s:=a.val.2
 simp_rw [add_assoc]
 exact congr_arg₂ (·-·) (congr_arg₂ (·-·) (congr_arg₂ (·+·) (hp ((x,r),i) j) (hp ((x+step r,s),i) j)) (hp ((x+step s,r),i) j)) (hp ((x,s),i) j)
lemma puff (G:Gauge): Albedo (linksQ G) (linksQ G) (finer moon):=by
 intro x y d; rcases x with ⟨⟨x,a⟩,i⟩; rw [site_roll,site_roll]
 unfold finer moon; rw [Finsupp.finsetSum_apply,Finsupp.finsetSum_apply]; apply sum_congr rfl; intro j _
 change dream (d+x,a) j i _= _; unfold dream; dsimp only; split_ifs <;> simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.zero_apply] <;> simp_rw [show ∀ s:Axis,d+x-step s=d+(x-step s) from fun s=>by abel] <;> try simp_rw [solar]
end YM.RegulatorIR.Oracle
