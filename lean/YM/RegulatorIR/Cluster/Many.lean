import YM.RegulatorIR.Cluster.Batch

/-! Nonempty cluster of columns. Layout index may include center and
geometry; same-order linearity over stencil coefficients. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W Z : Type}{X Y V U: W→ Type} {p i u n a b k r:ℕ} {L:Meter W}{d l:W→ℝ}{hl:∀ i,0<l i}
-- binary tree convenient (including mask-free reports)
inductive Composite (Z:Type)
 | atom : Z→ Composite Z
 | pair : Composite Z→Composite Z→Composite Z
namespace Composite
variable (J: Composite Z)
def In : Composite Z→ Z→Prop
 | atom z,y=>y=z
 | pair c d,y=> c.In y ∨ d.In y

def accounts (J:Composite Z)(S:Z→ℕ):ℕ:=match J with
 | atom z=>S z
 | pair c d=> accounts c S+accounts d S

def district (J:Composite Z)(S:Z→Set W) : Set W:= match J with
 | atom z=> S z
 | pair c d=> c.district S∪d.district S
lemma covers (J:Composite Z)(S:Z→Set W)(x:W) : x∈J.district S↔ ∃ i,J.In i∧x∈ S i:=by
 induction J with
 | atom i=> simp [district,In]
 | pair i j hi hj=> rw [district, mem_union, hi,hj]; simp only [In]; grind
-- admits repeats as slots (apart premise will control which inputs are arranged)
def Distinct (S:Z→Set Room)(t:ℝ) : Composite Z→ Prop
 | atom _=> True
 | pair a b=> Distinct S t a ∧ Distinct S t b ∧ ∀ i,a.In i → ∀ j,b.In j→ ∀ x∈S i,∀ y∈S j,t≤dist x y

def budget (J:Composite Z)(t:Z→ℝ≥0∞): ℝ≥0∞:=match J with
 | atom z=> t z
 | pair a b=> a.budget t*b.budget t

def product (J:Composite Z)(T: Z→ Orders W) : Orders W:= match J with
 | atom z=> T z
 | pair a b=> accord (a.product T) (b.product T)

lemma symmetric (J: Composite Z) (T:Z→Orders W)(h:∀ i,J.In i→gradedSymmetric (T i)): gradedSymmetric (J.product T):=by cases J with
 | atom i=>exact h i rfl
 | pair a b=> exact accord_sym _ _
lemma ranks (J:Composite Z)(T:Z→Orders W){c:Z→ℕ}(h:∀ i, J.In i→ Ranks (c i) (T i)): Ranks (J.accounts c) (J.product T):=by induction J with
 | atom i=>exact h i rfl
 | pair a b ih ih'=> exact rank_pair (ih fun i hi=> h i (Or.inl hi)) (ih' fun i hi=>h i (Or.inr hi))

variable {x:(w:W)→X w→Room}{S:Z→W→Set Room}
abbrev border (w:W)(S:Z→W→Set Room):= J.district (fun i=> S i w)
abbrev rent (w:W)(v:Z→W→ℝ≥0∞):= J.budget (fun i=>v i w)
variable {T:Z→(w:W)→Orders (X w)} {m:Z→ℕ} {v: Z→W→ℝ≥0∞}
structure Shaped (L:Meter W)(hl:∀ i,0<l i)(x:(i:W)→ X i→Room) (S:Z→W→Set Room) (v:Z→W→ℝ≥0∞)(d:W→ℝ)(u p:ℕ) (T:Z→(i:W)→Orders (X i))(m:Z→ℕ)(J:Composite Z):Prop where
 width : ∀ i,J.In i → Folds p L (estate hl x (S i) u) (v i) (T i)
 lit : ∀ i,J.In i→∀ j,(S i j).Nonempty
 shut : ∀ i,J.In i→∀ j,IsClosed (S i j)
 apart : ∀ w, Distinct (fun i=>S i w) (d w) J
 valence : ∀ i,J.In i→∀ w,Ranks (m i) (T i w)
 symmetric : ∀ i,J.In i→∀ w,gradedSymmetric (T i w)
 price : ∀ i,J.In i→∀ w, v i w≠⊤
 nonneg w: 0≤d w
namespace Shaped
variable {J B C: Composite Z}
lemma left (s:Shaped L hl x S v d u p T m (pair B C)): Shaped L hl x S v d u p T m B:= ⟨fun i hi=>s.width i (Or.inl hi),fun i hi=>s.lit i (Or.inl hi),fun i hi=>s.shut i (Or.inl hi),fun w=>(s.apart w).1,fun i hi=>s.valence i (Or.inl hi),fun i hi=>s.symmetric i (Or.inl hi),fun i hi=> s.price i (Or.inl hi), s.nonneg⟩
lemma right (s:Shaped L hl x S v d u p T m (pair B C)): Shaped L hl x S v d u p T m C:= ⟨fun i hi=>s.width i (Or.inr hi),fun i hi=>s.lit i (Or.inr hi),fun i hi=>s.shut i (Or.inr hi),fun w=>(s.apart w).2.1,fun i hi=>s.valence i (Or.inr hi),fun i hi=>s.symmetric i (Or.inr hi),fun i hi=> s.price i (Or.inr hi), s.nonneg⟩
lemma estate_shape (s:Shaped L hl x S v d u p T m J)(w:W): (J.border w S).Nonempty ∧ IsClosed (J.border w S) ∧ J.rent w v≠⊤:=by induction J with
 | atom i=> exact ⟨s.lit i rfl w,s.shut i rfl w,s.price i rfl w⟩
 | pair A B ih ih'=> refine ⟨(ih s.left).1.mono (subset_union_left ..), (ih s.left).2.1.union (ih' s.right).2.1, ENNReal.mul_ne_top (ih s.left).2.2 (ih' s.right).2.2⟩
lemma gather (s:Shaped L hl x S v d u p T m J): Folds p L (estate hl x (fun w=>J.border w S) u) (fun w=> J.rent w v) fun w=>J.product (fun i=> T i w):=by
 induction J with
 | atom i=>exact s.width i rfl
 | pair A B ih ih'=>
    have hx : Folds p L (estate hl x (fun w=>(pair A B).border w S) u) (fun w=>A.rent w v) fun w=> A.product (fun i=>T i w):= Folds.lesser u (fun w=> (s.left.estate_shape w).1) (fun _=>subset_union_left ..) (ih s.left)
    exact Folds.times hx (Folds.lesser u (fun w=>(s.right.estate_shape w).1) (fun _=>subset_union_right ..) (ih' s.right))
lemma graded (s:Shaped L hl x S v d u p T m J)(w): Ranks (J.accounts m) (J.product (fun i=>T i w)) ∧ gradedSymmetric (J.product (fun i=> T i w)):=⟨J.ranks _ (fun i hi=> s.valence i hi w),J.symmetric _ (fun i hi=> s.symmetric i hi w)⟩
lemma step_width (h:Shaped L hl x S v d (u+b) p T m (pair B C)): Widths p L hl x d (fun i=>B.border i S) (fun i=> C.border i S) u b (B.accounts m) (C.accounts m) (fun i=>B.rent i v) (fun i=> C.rent i v) (fun w=>B.product (fun i=>T i w)) (fun w=> C.product (fun i=>T i w)):=by
 refine ⟨?_,h.nonneg,fun w=>(h.left.estate_shape w).2.2,fun w=>(h.right.estate_shape w).2.2, h.left.gather, h.right.gather, fun w=>(h.left.graded w).1,fun w=>(h.right.graded w).1,fun w=>(h.left.graded w).2,fun w=>(h.right.graded w).2⟩
 intro w; refine ⟨(h.left.estate_shape w).1,(h.right.estate_shape w).1,(h.left.estate_shape w).2.1,(h.right.estate_shape w).2.1,?_⟩
 intro i hi j hj; obtain ⟨t,ht,hi'⟩:= (B.covers _ i).mp hi; obtain ⟨q,hq,hj'⟩:= (C.covers _ j).mp hj; exact (h.apart w).2.2 _ ht _ hq _ hi' _ hj'
end Shaped
end Composite

lemma accord_subL (T U Q:Orders W): accord (T-U) Q= accord T Q-accord U Q:=by
 ext1 e;ext1 i; rw [Pi.sub_apply,Pi.sub_apply, accord,accord,accord, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _
 rw [crisp,crisp,crisp,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl;intro u hu; rw [← Finset.mem_antidiagonal.mp hu]; simp only [pie]; change joined (T j.1 u.1-U j.1 u.1) (Q j.2 u.2)=joined _ _- joined _ _; unfold joined;rw [← symmetry_sub];apply congr_arg; funext x; exact sub_mul ..
lemma accord_subR (T U Q:Orders W): accord T (U-Q)=accord T U-accord T Q:=by
 ext1 e;ext1 i; rw [Pi.sub_apply,Pi.sub_apply, accord,accord,accord,← Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro j _; rw [crisp,crisp,crisp,← Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro u hu; rw [← Finset.mem_antidiagonal.mp hu];simp only [pie];change joined (T j.1 u.1) (U j.2 u.2-Q j.2 u.2)=joined _ _-joined _ _; unfold joined;rw [← symmetry_sub];apply congr_arg; ext1 x; exact mul_sub ..
end YM.RegulatorIR.Cluster
