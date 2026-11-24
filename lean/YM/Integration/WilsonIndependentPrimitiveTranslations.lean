import YM.Integration.WilsonIndependentConditionalNativeLinks
import YM.RegulatorIR.Profiles.Cadence

/-! Each actually submitted primitive, before the sum over centers, moves
with the physical coarse-cell translation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveTranslations
open Filter Function Lattice Wilson RG RegulatorIR RegulatorIR.Prim RegulatorIR.Diagram
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Geometry
open RegulatorIR.Oracle RegulatorIR.Calibration RegulatorIR.Halo RegulatorIR.Binding
open RegulatorIR.Ledger
open scoped Classical BigOperators

theorem rows {I X:Type}(V:Equiv.Perm I)(F:Equiv.Perm X)(T:X→Micro I)(Q:X→Orders I)(f:X→ℝ)(k:X→ℕ)
    (paid:∀i,Lab (k i) (f i) (T i) (Q i))(shift:∀i t v,T (F i) t v=T i t (v∘V))
    (cost:∀i,f (F i)=f i)(order:∀i,k (F i)=k i)(i:X)(e:ℕ):
    Q (F i) e=fun r=>echo V (Q i e r):=by
  have ha:=paid (F i);rw [cost,order] at ha;have hb:=paid i
  cases Nat.eq_zero_or_pos e with
  | inl h=>subst e;rw [ha.awake,hb.awake];rfl
  | inr h=>
    refine guessed (ha.scope_ e) ?_ (ha.smooth e) (fun r=>echo_sym (hb.smooth e r)) ?_
    · intro r hh;exact hb.scope_ e r (fun hz=>hh (by dsimp only;rw [hz,echo_zero]))
    intro x;rw [ha.figures x h,show flank (T (F i)) x=flank (T i) (x∘V) from funext fun t=>shift i t (t • x),
      ←hb.figures (x∘V) h]
    apply Finset.sum_congr rfl;intro j _
    dsimp only
    rw [strum_perm x V,show (fun z:Tuple I j=>echo V (Q i e j) (V∘z))=Q i e j from funext (echos _ _)]

def root (s:Cover):Equiv.Perm (Edge Cover):=Equiv.prodCongr (Equiv.addLeft s) (Equiv.refl _)
def roots (P:Patch)(s:Cover):Equiv.Perm Branchix:=Equiv.sumCongr (root (P.L.val • s)) (root s)

theorem original {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(s:Cover)(b:Branchix)(e:ℕ):
    let S:=C.rail K f;let T:=C.bore G Z t f
    T (roots S.patch s b) e=fun r=>echo (bundleS S s) (T b e r):=by
  intro S T
  apply rows (bundleS S s) (roots S.patch s) (prism S (bios S) (t f.prev)) T dry barkN (C.wheeled G Z t f) _
      (fun i=>by cases i<;>rfl) (fun i=>by cases i<;>rfl)
  rintro (x|x) τ v
  · change carnal S (bios S) (dis (strideR S s) x) τ v=carnal S (bios S) x τ (v∘bundleS S s)
    rw [carnal,carnal,branch_path];rfl
  change opi S _ (dis s x) τ v=opi S _ x τ _
  unfold opi
  change _*G.price (win G (v∘Sum.inr) _ * _)=_*G.price (win G ((v∘Sum.inr)∘carryX s) _ *
    (pond _ _ (win G ((v∘Sum.inl)∘carryX _)) _)⁻¹)
  rw [←carrier,←carrier,strideR,pulled (S:=S)]
  simp only [dis,Lattice.translate];rw [add_comm x.1]

end YM.Integration.WilsonIndependentPrimitiveTranslations
