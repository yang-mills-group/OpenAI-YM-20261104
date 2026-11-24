import YM.RegulatorIR.Epoch.Flat
import YM.RegulatorIR.Momentum.Gather

/-! Adapters and comparison Carry tickets for anchored *universal-cover*
progress. Used after contracting. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Filter Finset Lattice RG Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Uniform YM.RegulatorIR.Ledger Step Taping Precision Laurent Bloch Oracle Quadratic ENNReal
open RegulatorIR.Momentum (extent postage lamp Held anchored path trim)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y I:Type} {V: X→Type}{L: Meter X} {n u:ℕ}{l:ℝ}{K:X→ℝ≥0∞}
section static
variable (T:Packet (Long I) (n+1))(h:0<l)
def entryR (i:I): Tuple I n ≃ Hold (0:Fin (n+1)) i:=by
 refine ⟨fun x=>⟨Fin.cons i x,Fin.cons_zero ..⟩, fun x=>Fin.tail x.val, fun x=>Fin.tail_cons .., fun v=>Subtype.ext ?_⟩;dsimp only;generalize hx : (Fin.tail _) = q; subst q; -- dep rw
 ext1 j; induction j using Fin.cases; exact (Fin.cons_zero ..).trans v.property.symm;next j=> exact Fin.cons_succ ..

lemma pos_charge : ∀ x,Stalk.scopeQ (fun p:Tuple (Long I) (n+1)=>p 0) T (path h I u).diameter x≤ amount T u *4^u:=by
 intro x; unfold Stalk.scopeQ; rw [← quota_perm (entryR x)]; apply le_trans _ (mul_le_mul_left (bound_h T u x) _); rw [← quota_raised];apply quota_mono; exact fun i=> (Momentum.residence i x h).trans_eq (mul_comm ..)
lemma earns (he:IsSym T) : localQ (path h I u) T (amount T u * 4 ^u) := local_anchor _ 0 he (pos_charge T h)
lemma earnsP {c:ℝ≥0∞}(he: localQ (path h I u) T c): amount T u ≤ c*((1+n*5:ℝ≥0∞))^u:=by
 apply amount_cap;intro x; have ht:= he 0 x; unfold Stalk.scopeQ at ht; rw [← quota_perm (entryR x)] at ht; apply le_trans _ (mul_le_mul_left ht _);rw [← quota_raised]; apply quota_mono;intro i;exact (Momentum.living i x h).trans_eq (mul_comm ..)
lemma lamp_row (h:0<l)(L:Layer (Long I) (Long I)) : Layer.row L (Tariff.native l h u) (trim l) (trim l) (amount (lamp L) u * 4^u):=by
 intro i; have he:= pos_charge (u:=u) (lamp L) h i;unfold Stalk.scopeQ at he; rw [← quota_perm (entryR i),← quota_perm (Pert.Bulk.identify _).symm] at he; apply le_trans _ he;apply quota_mono;intro x
 let z:= ((entryR i (n:=1)) ((Pert.Bulk.identify (Long I)).symm x)).val; exact (path h I u).diameter_ge z 0 1
end static

def VacDay (Q:X→ℝ≥0∞)(K:Meter X)(V:∀ x,Tariff (V x))(F:(x:X)→Packet _ n) := ∃ p, Carry K Q p ∧∀ x,localQ (V x) (F x) (p x)
def RailDay (Q:X→ℝ≥0∞)(K:Meter X)(V:∀ x,Tariff (V x))(F:(x:X)→Layer _ _):=∃ p,Carry K Q p∧∀ x, Layer.row (F x) (V x) id id (p x)∧ Layer.row (Function.swap (F x)) (V x) id id (p x)
variable {D: X→ℝ} {V:I→Type} (h:∀ x,0< D x){T:X→Packet (Long Y) (n+1)}
lemma bonds_v (hp:Carry L K fun x=>amount (T x) u)(hs:∀ i,IsSym (T i)) :VacDay K L (fun x=>path (h x) Y u) T:= ⟨_,hp.mul_right (Poly.standard _ (show (4:ℝ≥0∞)^u≠⊤ by finiteness)), fun x=> earns (T x) (h x) (hs x) ⟩
lemma amount_profits (hp: VacDay K L (fun x=>path (h x) Y u) T): Carry L K (fun x=>amount (T x) u):=by obtain ⟨c,hc,H⟩:=hp;exact (hc.mul_right (Poly.standard _ (show (1+n*5:ℝ≥0∞)^u≠⊤ by finiteness))).mono (fun i=> earnsP (T i) (h i) (H i))
end YM.RegulatorIR.Epoch
