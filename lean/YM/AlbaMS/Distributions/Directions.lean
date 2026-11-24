import Mathlib.Analysis.Calculus.ContDiff.Bounds
import YM.Analysis.SmoothJets

/-!
# Price norms for position kernels

Many location weights (plane, inversion quotient, fixed-point defects). Want
one notion of kernel size bound. Price against all weighted, unbundled smooth
tests in ℝ. Common exponent growth; any fit order demanded. Directional-jet
version of the norm, so eg unchanged under pulling a test to joint nodes by a
slot projection, and respects testing on a sub-block of the coordinates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Testing
open Set Function Filter YM.Analysis
open scoped Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev Nice (f : E→F) := ContDiff ℝ ∞ f

lemma smooth_D (v : E) {f : E→F} (hf : Nice f) : Nice (D v f) := contDiff_iff_contDiffAt.mpr fun _=> dSmooth hf.contDiffAt v (by simp)

/-- Iterated derivatives, apply first listed direction first. -/
def nd : List E → (E→F) → E → F
| [],f => f
| x::L,f=> nd L (D x f)
@[simp] lemma nd_nil (f : E→F) : nd [] f=f := rfl
lemma nd_cons (v : E) (L : List E) (f : E→F) : nd (v::L) f=nd L (D v f) := rfl
lemma nd_sumlist (v w : List E) (f : E→F) : nd (v++w) f = nd w (nd v f) := by induction v generalizing f <;> simp only [nd_cons,List.cons_append,nd_nil,List.nil_append, *]
lemma nd_snoc (v : List E) (x : E) (f : E→F) : nd (v++[x]) f=D x (nd v f) := by rw [nd_sumlist]; rfl

lemma nd_nice (L : List E) {f : E→F} (hf : Nice f) : Nice (nd L f) := by induction L generalizing f with
  | nil => exact hf
  | cons v L ih => exact ih (smooth_D _ hf)

lemma nd_and_iter (n : ℕ) (p : Fin n → E) (x : E) {f : E→F} (h : Nice f) :
    nd (List.ofFn p) f x=iteratedFDeriv ℝ n f x p := by
  induction n generalizing f with
  | zero=> simp
  | succ n ih=>
    rw [List.ofFn_succ,nd_cons,ih (fun i=>p i.succ) (smooth_D (p 0) h)]
    have hh:=cons_inner (x:=x) (h.contDiffAt.of_le (show (↑(n+1:ℕ):WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) (p 0) (Fin.tail p)
    rw [Fin.cons_self_tail] at hh; exact hh.symm

lemma nd_iter (v : List E) (x : E) {f : E→F} (h : Nice f) : nd v f x=iteratedFDeriv ℝ v.length f x v.get := by
  rw [← nd_and_iter _ _ _ h,List.ofFn_get]

lemma nd_swap (x : E) (L : List E) {f : E→F} (hf : Nice f) : D x (nd L f)=nd L (D x f) := by
  induction L generalizing f with
  | nil => rfl
  | cons v L ih => rw [nd_cons, nd_cons, ih (smooth_D v hf), show D x (D v f)=D v (D x f) from funext fun i=> commuteD (hf.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top)) x v]
lemma nd_add (L : List E) {f g : E→F} (h : Nice f) (hh : Nice g) : nd L (f+g) = nd L f + nd L g := by
  induction L generalizing f g with
  | nil=> rfl
  | cons v L ih=>
    simp only [nd_cons]; rw [show D v (f+g)=D v f+D v g from funext fun i=> by rw [D, fderiv_add (h.differentiable (by simp) i) (hh.differentiable (by simp) i)]; rfl]; apply ih (smooth_D ..) (smooth_D ..)
    exact h
    exact hh
lemma nd_sub (L : List E) {f g : E→F} (h : Nice f) (hh : Nice g) : nd L (f-g) = nd L f - nd L g := by
  apply eq_sub_of_add_eq; rw [← nd_add L (f:=f-g) (h.sub hh) hh, sub_add_cancel]
lemma nd_scale (v : List E) (c : ℝ) {f : E→F} (h : Nice f) : nd v (c • f) = c • nd v f := by
  induction v generalizing f with
  | nil=> rfl
  | cons i v ih=> rw [nd_cons, nd_cons, show D i (c • f)=c • D i f from funext fun i=> by rw [D,fderiv_const_smul (h.differentiable (by simp) i)]; rfl, ih (smooth_D _ h)]
@[simp] lemma nd_zero (v : List E) : nd v (0:E→F)=0 := by
  simpa only [zero_smul] using (nd_scale v 0 (show Nice (0:E→F) from contDiff_const))
lemma nd_const_nonempty (i : E) (L : List E) (x : F) : nd (i::L) (fun _=>x)=0 := by
  rw [nd_cons, show (D i (fun _=>x))=0 from by funext j; simp [D], nd_zero]
lemma nd_mul_hits (v : E) {f g : E→ℝ} (h : Nice f) (hh : Nice g) : D v (f*g)=f*D v g+g*D v f := by
  funext x; rw [D,fderiv_mul (h.differentiable (by simp) x) (hh.differentiable (by simp) x)]; rfl

/-- Scaling all directions. -/
lemma nd_map_scalars (v : List E) (c : ℝ) {f : E→F} (h : Nice f) : nd (v.map (fun i=> c • i)) f=c^v.length • nd v f := by
  induction v generalizing f with
  | nil=> simp
  | cons i v ih=>
    rw [List.map_cons, nd_cons, show D (c • i) f=c • D i f from funext fun _=> map_smul .., nd_scale _ _ (smooth_D _ h), ih (smooth_D _ h),nd_cons, smul_smul]; simp [pow_succ']

lemma linear_pull (v : List E) (L : E→L[ℝ] X) (c : X) {f : X→F} (h : Nice f) :
    nd v (fun y=> f (c+L y))= nd (v.map L) f ∘ (fun y=> c+L y) := by
  induction v generalizing f with
  | nil => rfl
  | cons x v ih =>
    rw [List.map_cons,nd_cons,nd_cons,show D x (fun y=> f (c+L y)) = (fun y=>D (L x) f (c+L y)) from ?_, ih (smooth_D _ h)]
    funext z
    let P : E→ X:=fun y => c+L y
    have hp : HasFDerivAt P L z := L.hasFDerivAt.const_add c
    change fderiv ℝ (f∘P) z x=_; rw [fderiv_comp _ (h.differentiable (by simp) _) hp.differentiableAt,hp.fderiv]; rfl

/-- `W` is unnormalized. Test seminorm bound when tested after smooth position
restrictions. Using unbundled (also at radius 1). -/
def small (r : ℝ) (v : List E) := ∀ i∈v, ‖i‖ ≤ r
omit [NormedSpace ℝ E] in
lemma small_nil (r : ℝ) : small (E:=E) r [] := by simp [small]
omit [NormedSpace ℝ E] in
@[simp] lemma small_cons {r : ℝ} {x : E} {v : List E} : small r (x::v) ↔ ‖x‖ ≤ r ∧ small r v := by simp [small]
omit [NormedSpace ℝ E] in
@[simp] lemma small_append {r : ℝ} {x v : List E} : small r (x++v) ↔ small r x ∧ small r v := by simp [small]; grind
lemma map_radius (L : E→L[ℝ] X) {r s : ℝ} (h : ∀ x, ‖x‖≤r → ‖L x‖≤s) (v : List E) (hp : small r v) : small s (v.map L):= by
  intro i hi; obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hi; exact h _ (hp _ hx)

/-- Ungraded derivative-test seminorm bound through `j`. -/
structure Budget (r : ℝ) (j : ℕ) (W : E→ ℝ) (f : E→F) : Prop where
  nice : Nice f
  rate : ∀ x v, v.length≤ j → small r v → ‖nd v f x‖ ≤ W x

namespace Budget
variable {r s : ℝ} {j i k : ℕ} {W U V : E → ℝ} {B : X→ℝ} {f g : E→ F}
lemma actual (h : Budget r j W f) (x) : ‖f x‖ ≤ W x := h.rate x [] (Nat.zero_le _) (small_nil _)
lemma sign (h : Budget r j W f) : 0 ≤ W := fun i=> (norm_nonneg _).trans (h.actual i)
lemma ascent (h : Budget r j W f) (hp : W ≤ U) : Budget r j U f := ⟨h.nice,fun x v hi he=> (h.rate x v hi he).trans (hp x)⟩
lemma radius (h : Budget r j W f) (hr : s≤r) : Budget s j W f := ⟨h.nice,fun x v hp hv=> h.rate x v hp fun i h=> (hv i h).trans hr⟩
lemma rank (h : Budget r j W f) (hp : k≤j) : Budget r k W f := ⟨h.nice,fun x v hi=> h.rate x v (hi.trans hp)⟩
lemma zero (h : 0≤W) : Budget r j W (0:E→F) := ⟨contDiff_const,fun i _ _ _=> by simpa using h i⟩
lemma const (x : F) (h : ∀ i, ‖x‖ ≤ W i) : Budget r j W (fun _=> x) := by
  refine ⟨contDiff_const,?_⟩; intro i v _ _; cases v with
  | nil=> exact h _
  | cons a v=> rw [nd_const_nonempty,Pi.zero_apply,norm_zero]; exact (norm_nonneg _).trans (h i)
lemma add (h : Budget r j W f) (hh : Budget r j U g) : Budget r j (W+U) (f+g):= by
  refine ⟨h.nice.add hh.nice,?_⟩; intro x v hj hv; rw [nd_add v h.nice hh.nice, Pi.add_apply]; exact (norm_add_le ..).trans (add_le_add (h.rate x v hj hv) (hh.rate x v hj hv))
lemma sub (h : Budget r j W f) (hh : Budget r j U g) : Budget r j (W+U) (f-g):= by
  refine ⟨h.nice.sub hh.nice,?_⟩; intro x v hj hv; rw [nd_sub v h.nice hh.nice, Pi.sub_apply]; exact (norm_sub_le ..).trans (add_le_add (h.rate x v hj hv) (hh.rate x v hj hv))
lemma smul (h : Budget r j W f) (c : ℝ) : Budget r j (‖c‖ • W) (c • f) := by
  refine ⟨h.nice.const_smul _,?_⟩; intro x v hp he; rw [nd_scale _ _ h.nice,Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (h.rate x v hp he) (norm_nonneg _)
lemma drop (h : Budget r j W f) (v : E) (hv : ‖v‖ ≤ r) (hk : k<j) : Budget r k W (D v f) :=
    ⟨smooth_D _ h.nice,fun x l hi he=> h.rate x (v::l) (Nat.succ_le_of_lt (lt_of_le_of_lt hi hk)) (small_cons.mpr ⟨hv,he⟩)⟩
lemma mul {f g : E→ℝ} (h : Budget r j W f) (hb : Budget r j U g) : Budget r j ((2: ℝ)^j • (W*U)) (f*g):= by
  induction j generalizing f g with
  | zero=>
    refine ⟨h.nice.mul hb.nice,?_⟩; intro x v hv _; obtain rfl:= List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hv); rw [nd_nil,Pi.mul_apply,norm_mul,pow_zero,one_smul]; exact mul_le_mul (h.actual x) (hb.actual x) (norm_nonneg _) (h.sign x)
  | succ j ih =>
    have he : Budget r j ((2:ℝ)^j • (W*U)) (f*g):= ih (h.rank (Nat.le_succ _)) (hb.rank (Nat.le_succ _))
    refine ⟨he.nice,?_⟩; intro x v hv hr; cases v with
    | nil=> refine (he.actual x).trans (show ( ((2:ℝ)^j • (W*U))) x ≤ _ from ?_); change _*(W x*U x) ≤ _*(W x*U x); gcongr
            exact mul_nonneg (h.sign x) (hb.sign x)
            norm_num
            omega
    | cons a v=>
      obtain ⟨ha,hr⟩:= small_cons.mp hr
      rw [nd_cons,nd_mul_hits a h.nice hb.nice]
      have h1:= ih (h.rank (Nat.le_succ _)) (hb.drop a ha (Nat.lt_succ_self _))
      have h2:= ih (h.drop a ha (Nat.lt_succ_self _)) (hb.rank (Nat.le_succ _))
      have H := h1.add (show Budget r j _ (g*D a f) from (mul_comm (D a f) g) ▸ h2)
      rw [pow_succ',mul_smul,two_smul]; exact H.rate x v (Nat.le_of_succ_le_succ hv) hr
lemma push (L : E→L[ℝ] X) (a : X) {f : X→ F} (h : Budget r j B f) (hr : ∀ i, ‖i‖≤s→‖L i‖≤ r) : Budget s j (fun x=> B (a + L x)) (fun x=> f (a+L x)) := by
  refine ⟨h.nice.comp (contDiff_const.add L.contDiff),?_⟩; intro i v hx he; rw [linear_pull v L a h.nice]; exact h.rate (a+L i) _ ((List.length_map ..).le.trans hx) (map_radius L hr _ he)
lemma swell (h : Budget r j W f) (c : ℝ) (hc : 1 ≤ c) : Budget (c*r) j (c^j • W) f := by
  refine ⟨h.nice,?_⟩; intro i v hp he
  have hz : 0<c:=zero_lt_one.trans_le hc
  let w:= v.map (c⁻¹ • ·)
  have hw : small r w := by
    intro i hi; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hz).le]; exact (mul_le_mul_of_nonneg_left (he _ ha) (inv_pos.mpr hz).le).trans_eq (inv_mul_cancel_left₀ hz.ne' _)
  have ht : w.length = v.length:=List.length_map ..
  rw [show v=w.map (c • ·) from ?_,nd_map_scalars w c h.nice, ht,Pi.smul_apply,norm_smul,Real.norm_of_nonneg (pow_pos hz _).le]
  · change _ ≤ _ * W i
    apply (mul_le_mul_of_nonneg_left (h.rate i w (ht.le.trans hp) hw) (pow_pos hz _).le).trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hp) (h.sign i)
  unfold w; rw [List.map_map,show (fun x:E=>c • x) ∘ (fun x:E=>c⁻¹ • x)=id from funext fun i=> smul_inv_smul₀ hz.ne' i,List.map_id]
end Budget

end YM.MSBar.Testing
