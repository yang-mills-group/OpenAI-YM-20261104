import YM.MS.TaylorCharge
/-!
# Vanishing of the low Taylor anomaly

Using only same-chart constraints. Conditional on the two quantum identities,
will instantiate below. `Closed` is at rank, not on shell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Finset Koszul Flux Wire Real Domain LogTime LogTime.IntervalFamily
open scoped Topology ContDiff
variable {A P E ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype A] {S : LogTime.IntervalFamily ι}
   {p : Sector A} {Z Y : Charge p P ℂ} {m : A → ℤ} {h u:ℤ} {w: Wire A E P} {b : Bool} {r d : ℕ} {y : ℝ}

omit [Fintype A] [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma visit_shape {w : Legs (Mode A P)} {f : E→Slash A P ℂ} (H : ∀ l i k, l++i::k=w → Shape (fun x : E=> f x l i k) h) : Shape (fun x:E=>visit b p w (f x)) h := by
   induction w generalizing f with
   | nil=> exact form_zero _
   | cons i w ih=> exact (H [] i w rfl).add ((ih (f:=fun x l a k=> f x (i::l) a k) (fun l a k he=> H _ _ _ (by simp [he]))).scalar (cross b (p i.1))) -- scalar parameter order?
lemma charge_form {f: Row A P ℂ} (H : Charge.Criteria S m y Z Y) (hc : Form f m h b) : Form (Y.raise f) m (h+1) b:= by
   intro X _ _ w hw; unfold fieldVal; simp_rw [visit_Z,visit_sail]; refine visit_shape (fun l i k hp=>?_); rcases i with ⟨a,q⟩
   let U (j:A) := l++(j,q)::k; let V (j:A) (x:X):= Y.table a j (q x)*f (sail (U j) x)
   have hv j : Shape (V j) (h+1-fieldDim m w) := by
       have he := hc X (U j) (visit_course b l k (a,q) (hp ▸ hw) j)
       have hd : fieldDim m (U j)=fieldDim m w-m a+m j:= by rw [← hp]; exact visit_field m l k (a,q) j
       convert (((H.shape a j).linear q).mul he) using 1; rfl; rw [hd]; omega
   convert Shape.sum (s:=Finset.univ) (fun j _=>hv j) using 1; ext; rw [Finset.sum_apply]; simp [V,U]

lemma burn_cost {K H F G : Clock ι → Row A P ℂ} (hs : Charge.Criteria S m y Z Y)
   (hp : Course b w) (hl : ∀ t w', Course b w' → w'.length=w.length → Z.raise (F t) w' = H t w')
   (hm : ∀ t w', Course b w' → w'.length=w.length → Y.raise (G t) w' = K t w')
   (hc : Light S.primary (rate S y) m (lane S H) (lane S K) w (h+1))
   (ho : ∀ w': Wire A E P, Course b w' → w'.length=w.length → herecost S G w' h m) :
   Bound S.primary (Chart (lane S (fun i => Z.raise ((F-G) i))) w) fun i=> S.primary.length i ^ (fieldDim m w-(h+1))*rate S y i := by
   unfold Light at hc
   have ht:= (hc.gain).sub (Z.delta_cost Y (fun i=> exp_pos _ |>.le : ∀ i,0≤ rate S y i) hs.cost hp ho)
   convert! ht using 1; funext i x; simp only [lane,Chart,Pi.sub_apply,map_sub, hl _ _ (sail_course x hp) (sail_len ..), ← hm _ _ (sail_course x hp) (sail_len ..)]; abel

section
variable (H : Charge.Criteria S m y Z Y) (hi : ∀ i, S.window i=Set.Ici (S.beg i)) (hy : 0<y) (ht : y<1) (u : ℤ) {M : Clock ι → Row A P ℂ} {Q : Row A P ℂ} {w : Legs (Mode A P)}
abbrev Lit (b : Bool) (m : A→ℤ) (r : ℕ) (M : Clock ι → Row A P ℂ) (Q : Row A P ℂ) (u:ℤ) (i:ι) := ∀w' : Legs (Mode A P), Course b w'→w'.length=r → ∀ j:ℕ, fieldDim m w'+j≤u → Tendsto (fun t=> torch j (M (i,t)) w') atTop (𝓝 (if fieldDim m w'+j=u then Q w' else 0))

def Frozen (b : Bool) (m : A→ℤ) (r:ℕ) (M : Clock ι → Row A P ℂ) (Q : Row A P ℂ) (u:ℤ) (i:ι) := Lit b m r M Q u i ∧ Form Q m u b
include H hi hy ht
theorem class_kernel (hh : u≤h) (hp : Course b w) (hc : ∀ w': Legs (Mode A P), Course b w' → w'.length=w.length → ∀ t, ContDiff ℝ ∞ (fieldVal (M t) (ray w'))) (i : ι) (hd : Frozen b m w.length M Q u i) (H0 : Bound S.primary (Chart (lane S (fun i=> Z.raise (M i))) (ray w)) fun i=> S.primary.length i ^ (fieldDim m w-(h+1))*rate S y i) :
   Y.raise Q w=0:= by
   cases hd with | intro hl hd =>
   haveI : Nonempty ι:= ⟨i⟩
   rcases lt_or_ge (u+1) (fieldDim m w) with h1|h1
   · have hq := charge_form H hd ℝ _ (ray_course hp)
     have h' : u+1-fieldDim m (ray w)<0:=by rw [ray_dim]; omega
     exact Eq.trans (congr_arg (Y.raise Q) (ray_sail w).symm) (congr_fun (hq.charge h') 1) -- ignoring hi etc ok
   let j:=(u+1-fieldDim m w).toNat; have hj : fieldDim m w+j=u+1:=by unfold j; omega
   have hz:= Charge.torch_limit H hi hy (fun t=> M (i,t)) Q u hp j hj (fun a he h t=>hc a he h _) hd hl
   apply tendsto_nhds_unique hz
   have hj := (int_need hy ht).2 (show fieldDim m w-(h+1)+j≤0 by omega)
   have hb := zero_taylor hi hj (f:=tape (fun i=> Z.raise (M i)) (ray w)) H0 i
   let L : (ℝ [×j]→L[ℝ] ℂ) →L[ℝ] ℂ:= (Nat.factorial j:ℝ)⁻¹ • ContinuousMultilinearMap.apply ℝ (fun _=>ℝ) ℂ (fun _=>1)
   have hv := (L.continuous.tendsto 0).comp hb; rw [map_zero] at hv; convert hv using 1; rfl
end
end YM.MS.Plane
