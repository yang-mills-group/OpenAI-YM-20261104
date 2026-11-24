import YM.MS.RayRules
/-! # The elementary syntax of replacing exactly one leg. Use split parity signs
in Q and in checking symmetries. Need versions on marks. No factor from identical
letters beyond list derivative convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Set Finset Koszul Wire
variable {A P E ι R : Type} {p : Sector A} [CommRing R]

abbrev Slash (A P R : Type) := Legs (Mode A P) → Mode A P → Legs (Mode A P) → R

def visit (b : Bool) (p : Sector A) : Legs (Mode A P) → Slash A P R → R
| [],_ => 0
| i::w,U=> U [] i w + cross b (p i.1)*visit b p w (fun l a k=> U (i::l) a k)

lemma visit_cons (b p) (i : Mode A P) (w) (U: Slash A P R) : visit b p (i::w) U = U [] i w+ cross b (p i.1)*visit b p w (fun l a k=>U (i::l) a k) := rfl
lemma visit_nil (b p) (U : Slash A P R) : visit b p [] U=0:= rfl

lemma visit_Z [Fintype A] (Z:Charge p P R) (F:Row A P R) w : Z.raise F w=visit true p w (fun l i r=> ∑ j:A,Z.table i.1 j i.2*F (l++(j,i.2)::r)) := by
   induction w generalizing F with
   | nil => simp [Charge.raise,visit_nil]
   | cons i w ih => rcases i with ⟨i,q⟩; rw [Charge.act_at,ih,visit_cons]; simp [at_D]
lemma visit_agree (b p) {w : Legs (Mode A P)} {U V : Slash A P R} (h : ∀ l i k, l++i::k=w → U l i k=V l i k) : visit b p w U=visit b p w V:= by
   induction w generalizing U V with
   | nil => rfl
   | cons i w ih=> rw [visit_cons,visit_cons,h [] i w rfl,ih (U:=fun l a k=> U (i::l) a k) (V:=fun l a k=> V (i::l) a k) (fun l a k he=> h _ _ _ (by simp [he]))]
variable {b : Bool}
lemma visit_add (w) (U V : Slash A P R) : visit b p w (fun l i k=> U l i k+V l i k)=visit b p w U+visit b p w V:= by
   induction w generalizing U V with
   | nil=> simp [visit] -- name
   | cons i w ih=> simp only [visit_cons,ih,mul_add]; abel
lemma visit_neg (w) (U : Slash A P R) : visit b p w (fun l i k=> -U l i k)= -visit b p w U:= by
   induction w generalizing U with
   | nil=> simp [visit]
   | cons i w ih=> simp only [visit_cons,ih,mul_neg]; abel
lemma visit_sub (w) (U V : Slash A P R) : visit b p w (fun l i k=> U l i k-V l i k)=visit b p w U-visit b p w V:= by simp_rw [sub_eq_add_neg,visit_add,visit_neg]
lemma visit_zero (w) : visit b p (P:=P) (R:=R) w (fun _ _ _=>0)=0:= by induction w <;> simp_all [visit_cons,visit_nil]

variable [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma visit_sail (x : E) (w : Wire A E P) (U : Slash A P R) : visit b p (sail w x) U=visit b p w (fun l i k => U (sail l x) (i.1,i.2 x) (sail k x)) := by
   induction w generalizing U with
   | nil=> rfl
   | cons i w ih=> rw [sail_cons,visit_cons,visit_cons,ih]; rfl

variable {w : Legs (Mode A P)} {V : E→Slash A P ℂ}
omit [NormedSpace ℝ P] in
lemma visit_course h (l k : Legs (Mode A P)) (q : Mode A P) (g : Course h (l++q::k)) j : Course h (l++(j,q.2)::k):= by
   intro hx; simpa using g hx
omit [NormedSpace ℝ P] [NormedAddCommGroup P] in
lemma visit_field (m : A → ℤ) l k (q : Mode A P) (j:A) : fieldDim m (l++(j,q.2)::k) = fieldDim m (l++q::k)-m q.1 + m j:= by
   unfold fieldDim; simp; ring

section visitFun
open scoped Topology ContDiff
omit [NormedSpace ℝ P] [NormedAddCommGroup P]
-- prefer E param independent type so also use chart functions
lemma visit_diff {i : ℕ∞} (h : ∀ l i' k, l++i'::k=w → ContDiff ℝ i (fun x : E=> V x l i' k)) : ContDiff ℝ i (fun x=> visit b p w (V x)):= by
   induction w generalizing V with
   | nil=> exact contDiff_const
   | cons q w ih=> refine (h [] q w rfl).add (contDiff_const.mul (ih (V:=fun x l a k=> V x (q::l) a k) ?_)); exact fun l a k ht=> h _ _ _ (by simp [ht])
lemma visit_bound {S : Scale ι} {L : ι → E→Slash A P ℂ} {f:ι→ℝ} (hp : ∀ i, 0≤ f i) (h : ∀ l i' k, l++i'::k=w → Bound S (fun i (x : E)=> L i x l i' k) f) : Bound S (fun i x=> visit b p w (L i x)) f:= by
   induction w generalizing L with
   | nil=> exact Costs.zero (fun i _ _=> hp i)
   | cons q w ih=> refine Costs.add (h [] q w rfl) (Costs.L (ContinuousLinearMap.mul ℝ ℂ (cross b (p q.1))) (ih (L:=fun i x l a k=> L i x (q::l) a k) ?_)); exact fun l a k ht=> h _ _ _ (by simp [ht])
lemma visit_limit {a : Filter ι} {F : ι→Slash A P ℂ} {K : Slash A P ℂ} (h : ∀ l i k,l++i::k=w → Filter.Tendsto (fun x=>F x l i k) a (𝓝 (K l i k))) : Filter.Tendsto (fun x=> visit b p w (F x)) a (𝓝 (visit b p w K)):= by
   induction w generalizing F K with
   | nil=> exact tendsto_const_nhds
   | cons q w ih=> refine (h [] q w rfl).add ( Filter.Tendsto.const_mul _ (ih (K:=fun l i k=> K (q::l) i k) (F:=fun x l i k=>F x (q::l) i k) ?_)); exact fun l a k ht=> h _ _ _ (by simp [ht]) -- order
lemma visit_read {V : ℝ→Slash A P ℂ} {j : ℕ} (h : ∀ l i' k, l++i'::k=w → ContDiff ℝ ∞ (fun x : ℝ=> V x l i' k)) : reading j (fun x=> visit b p w (V x)) = visit b p w (fun l i k=> reading j (fun x=>V x l i k)) := by
   induction w generalizing V with
   | nil=> simp [visit_nil,reading]
   | cons q w ih=>
       let W (x:ℝ) (l) i k := V x (q::l) i k; have hw l i k (he : l++i::k=w) : ContDiff ℝ ∞ (fun x : ℝ=> W x l i k):=h _ _ _ (by simp [he])
       simp_rw [visit_cons]; rw [read_add (h [] _ _ rfl) (contDiff_const.mul (visit_diff (b:=b) (p:=p) hw)), read_const, ih hw]
end visitFun
end YM.MS.Plane
