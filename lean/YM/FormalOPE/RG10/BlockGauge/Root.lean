import YM.FormalOPE.RG10.BlockGauge.Prediction
/-!
 # Root truss for diagram evaluation (algebraic properties)

 Many observables used in comparison and OPE calculations straddle a scale boundary.
 Instead of introducing at each step a new calculus of which gauge fixings
 give rise to the same insertion polynomial, propose using a joint graph for the diagram.
 This is for *diagrammatic calculation*, finite regulator. It needn't be used to invert any large
 system of equations when calculating diagrams; one ambition is to be able to derive
 block elimination algorithms (incl. changing gauges at blocking, reclosure and projection)
 **from** joint graph quantities.

 A rooted quiver (parallel edges very much allowed) and an oriented spanning tree choice.
 For our application vertex is coalesced by the inversion convention and **shared** across levels
 (gauge acts once at a vertex).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge

structure Loom (V E : Type) where
  origin : V
  fromEdge : E → V
  toEdge : E → V

variable {V E : Type}
namespace Loom
variable (D : Loom V E)
-- height just certifies acyclicity and hence termination; can use a forest at one layer topped
-- off with a tree on next layer etc.
structure Truss where
  height : V → ℕ
  parent (v : V) (h : v ≠ D.origin) : V
  descend (v : V) (h : v ≠ D.origin) : height (parent v h)<height v
  wire (v : V) (h : v ≠ D.origin) : E
  orientation (v : V) (h : v ≠ D.origin) :
   (D.fromEdge (wire v h) = parent v h ∧ D.toEdge (wire v h) = v)
   ∨ (D.fromEdge (wire v h) = v ∧ D.toEdge (wire v h) = parent v h)
variable {K : Type} [Group K]
def spin (g : V → K) (u : E → K) (e : E) : K:= g (D.fromEdge e) * u e * (g (D.toEdge e))⁻¹
@[simp] lemma spin_one (u : E → K) : D.spin 1 u=u := by ext1 e; simp [spin]
lemma spin_chain (g h : V → K) (u : E → K) : D.spin g (D.spin h u)=D.spin (g*h) u := by ext1 e; simp [spin, mul_assoc]
namespace Truss
variable {D}
open scoped Classical
variable (T : D.Truss)
def Branch (e : E) := ∃ (v:V) (h:v ≠ D.origin), T.wire v h=e
abbrev Tree := { e // T.Branch e }
abbrev Bulk := { e // ¬ T.Branch e }
lemma wire_branch (v : V)(h : v ≠ D.origin): T.Branch (T.wire v h):=⟨v,h,rfl⟩
lemma distinguish (x y : V) (hx : x≠D.origin)(hy : y≠D.origin)(H : T.wire x hx=T.wire y hy): x=y := by
 have a := T.orientation x hx
 have b := T.orientation y hy
 have p := T.descend x hx
 have q := T.descend y hy
 rw [H] at a
 rcases a with ⟨a₁,a₂⟩|⟨a₁,a₂⟩ <;> rcases b with ⟨b₁,b₂⟩|⟨b₁,b₂⟩
 · exact a₂.symm.trans b₂
 · exact False.elim ((Nat.lt_asymm p) (by rw [←a₁,b₁]; rwa [←b₂,a₂] at q)) -- check lt_asymm
 · exact False.elim ((Nat.lt_asymm p) (by rw [←a₂,b₂]; rwa [←b₁,a₁] at q))
 exact a₁.symm.trans b₁
-- tree gauge puts all selected tree links to one, root untouched.
def toward (v:V)(h:v≠D.origin)(u: E → K) : K := if D.toEdge (T.wire v h) = v then u (T.wire v h) else (u (T.wire v h))⁻¹

def frame (u:E→K)(v:V) : K :=
 if h:v ≠ D.origin then frame u (T.parent v h) * T.toward v h u else 1
termination_by T.height v
decreasing_by exact T.descend v _
@[simp] lemma frame_root (u:E→K) : T.frame u D.origin=1 := by rw [frame,dif_neg (not_not.mpr rfl)]
lemma frame_parent (u:E→K) (v:V) (h:v≠D.origin) : T.frame u v=T.frame u (T.parent v h)*T.toward v h u:= by rw [frame,dif_pos h]
lemma toward_gauge (u : E → K)(g : V → K)(v:V)(h:v≠D.origin) :
 T.toward v h (D.spin g u) = g (T.parent v h) * T.toward v h u * (g v)⁻¹:= by
 rcases T.orientation v h with ⟨hh,h₂⟩|⟨hh,h₂⟩
 · simp_rw [toward,spin,h₂,hh, if_true]
 have ht:= ne_of_lt (T.descend v h)
 have hu: T.parent v h≠v:=fun e=> ht (congr_arg (T.height) e)
 simp [toward,spin,h₂,hh,hu,mul_assoc]
lemma frame_gauge_aux (u : E → K)(g : V → K)(v:V):
 T.frame (D.spin g u) v = g D.origin * T.frame u v * (g v)⁻¹:= by
 by_cases hh : v = D.origin
 · subst v; simp
 rw [T.frame_parent _ v hh, T.toward_gauge, T.frame_parent _ v hh, frame_gauge_aux u g (T.parent v hh)]
 group
termination_by T.height v
decreasing_by exact T.descend v _
lemma frame_gauge (u : E → K)(g : V → K)(h:g D.origin=1) : T.frame (D.spin g u)=T.frame u*g⁻¹:= by
 ext1 v; simp [T.frame_gauge_aux,h]

-- operations on joint model over arbitrary compact structure group
 def treeGauge (u:E→K) : E → K := D.spin (T.frame u) u
lemma identify (u : E → K)(g:V→K) (h:g D.origin=1) : T.treeGauge (D.spin g u)= T.treeGauge u:= by
 rw [treeGauge,T.frame_gauge _ _ h,D.spin_chain,(by group:T.frame u*g⁻¹*g=T.frame u)]; rfl
lemma toward_gauge_one (u : E → K)(v:V)(h:v≠D.origin) : T.toward v h (T.treeGauge u)=1:=by rw [treeGauge,toward_gauge,T.frame_parent _ v h]; group
lemma fixes_tree (u:E→K)(e:E)(h : T.Branch e): T.treeGauge u e=1:= by
 obtain ⟨v,h,rfl⟩:=h
 have H:= T.toward_gauge_one u v h; unfold toward at H; split at H
 · exact H
 exact inv_eq_one.mp H
lemma frame_only (u y:E→K)(h: ∀ i, T.Branch i → u i=y i)(v : V): T.frame u v=T.frame y v:= by
 by_cases hh : v = D.origin
 · subst v; simp
 rw [T.frame_parent _ _ hh, T.frame_parent _ _ hh, frame_only u y h (T.parent v hh)]
 unfold toward; rw [h _ (T.wire_branch v hh)]
termination_by T.height v
decreasing_by exact T.descend _ _
lemma unit_frame (v:V): T.frame (1:E→K) v=1:= by
 by_cases hh:v=D.origin
 · subst v; simp
 rw [T.frame_parent _ _ hh, unit_frame (T.parent v hh)]; simp [toward]
termination_by T.height v
decreasing_by exact T.descend _ _
lemma already (u:E→K)(h:∀ i, T.Branch i→u i=1): T.treeGauge u=u := by rw [treeGauge,show T.frame u=1 from funext fun v=> (T.frame_only u (1:E→K) h v).trans (T.unit_frame v)]; simp
end Truss
end Loom
end YM.FormalOPE.RG10.BlockGauge
