import YM.XSpace.Numer
/-!
# At the paired curvature end: one universal elementary expression to leading order

Exact at finite α modulo Surface, whose power we use separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chiral Litter Mu Tide Scale Pages Sail Chart2 Finsupp MvPolynomial Source
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d e:ℕ} {H:Hol G} (g:G.Simple)(S:Survey G H d)
def drawΦ (V:Axis→Toe)(u:PlaqAxes) := D (six u) (V (endr u)) - D (endr u) (V (six u))
def drawn (σ:Bool)(p:P)(V:Axis→Toe): Toe:=∑ u:PlaqAxes,q σ p (six u) (endr u) • drawΦ V u
abbrev core (σ:Bool)(p:P) (i:G.ColorIndex)(x:Cover): Line G:=∑ u:PlaqAxes,q σ p (six u) (endr u) • Trace.touch x (six u) (endr u) [] i
def surveyed (σ:Bool)(p:P)(V:Axis→Toe):Toe:= ∑ i:Fin S.size,coupon g S σ p i • mov (S.looks i).offset (drawΦ V (S.looks i).plaq)
lemma crevice (V:Axis→Toe){k:ℕ}(h:∀ v,V v∈ Terrain k)(u:PlaqAxes):drawΦ V u∈ Terrain (k+1):= Submodule.sub_mem _ (steps_hill (h _) _) (steps_hill (h _) _)
lemma sustained (V:Axis→Toe){k:ℕ}(h:∀ v,V v∈Terrain k)(σ:Bool)(p:P): drawn σ p V∈ Terrain (k+1) ∧ surveyed g S σ p V∈Terrain (k+1):=by
  unfold drawn surveyed; constructor
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (crevice V h i)
  exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (slide_hill (crevice V h _) _)
lemma drawing (V X:Axis→Toe){k:ℕ}(h:∀ i,V i-X i∈ Surface k)(σ:Bool)(p:P): drawn σ p V -drawn σ p X∈ Surface (k+1):=by
  unfold drawn drawΦ; rw [← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i _; rw [← smul_sub,sub_sub_sub_comm, ← map_sub, ← map_sub]; exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (steps_deriv (h _) _) (steps_deriv (h _) _))
lemma participation (he:2≤d)(V:Axis→Toe){k:ℕ}(h:∀ i,V i∈Terrain k)(σ:Bool)(p:P): surveyed g S σ p V-drawn σ p V∈ Surface (k+1):=by
  unfold surveyed drawn; rw [← stage g S σ p (drawΦ V) he,← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i _; rw [← smul_sub]; exact Submodule.smul_mem _ _ (safekeeping (crevice V h _) _)
abbrev magnetic (σ τ:Bool)(p r:P):=drawn σ p (field τ r)

lemma canon_pairs (σ τ:Bool)(p:P)(r:Name G)(x y:Cover)(j:G.ColorIndex): handshake (core σ p j x) (cable g S τ r y) = χ r.2 j*drawn σ p (Mn g S τ r.1) (x-y):=by
  let V:=Mn g S τ r.1; unfold core handshake drawn; rw [map_sum,LinearMap.sum_apply,Finset.sum_apply,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,LinearMap.smul_apply]; change q σ p _ _ * handshake _ _= _ * (q σ p _ _ * drawΦ V i (x-y)); rw [Φ_probe, mul_left_comm]; rfl
lemma brush (x v:Cover)(i j:Axis)(c:G.ColorIndex): displace x (Trace.touch v i j [] c)=Trace.touch (v+x) i j [] c:=by unfold Trace.touch; simp only [_root_.map_sub,toll,pin,radius,add_comm v]
lemma cup (T:Survey G H e) (σ τ:Bool)(p r:Name G)(x y:Cover): handshake (cable g S σ p x) (cable g T τ r y)= χ r.2 p.2 * surveyed g S σ p.1 (Mn g T τ r.1) (x-y):=by
  let V:= Mn g T τ r.1; unfold surveyed handshake; rw [cable, wickLine]; simp_rw [map_sum,LinearMap.sum_apply, Finset.sum_apply,map_smul,LinearMap.smul_apply,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [brush]; let u:=S.looks i; change (coupon g S σ p.1 i)* handshake _ _=χ r.2 p.2 * (coupon g S σ p.1 i * drawΦ V u.plaq (u.offset+(x-y))); rw [Φ_probe,mul_left_comm, show u.offset+(x-y)=u.offset+x-y from (add_sub_assoc ..).symm]; rfl
lemma phrase (T:Survey G H e)(hd:2≤d)(he:2≤e)(σ τ:Bool)(p r:P): surveyed g S σ p (Mn g T τ r)-magnetic σ τ p r∈ Surface 4:=by rw [← sub_add_sub_cancel _ (drawn σ p (Mn g T τ r)) _]; exact Submodule.add_mem _ (participation g S hd _ (fun i=> shared g T τ r i) σ p) (drawing _ _ (fun k=> stashed g T τ r he k) σ p)
end YM.XSpace.Relief
