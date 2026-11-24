import YM.MS.BadFactor
/-!
# Closure of the lowest nonvanishing Taylor dimension

The key advantage of using the high-momentum flow here is we can prove this
property without taking a continuum limit of bare vertices termwise. All estimates
pay on the low-scale discrepancy and on the smoothed Laplacian + binary bracket RHS.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Finset LogTime Real Koszul
open scoped Topology ContDiff
open LogTime.IntervalFamily Wire
variable {ι P E A : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
   {p: Sector A} {b:Bool} {m:A→ℤ} {R:IntervalFamily ι} {y:ℝ}
namespace Charge

structure Criteria (R : IntervalFamily ι) (m : A→ℤ) (y:ℝ) (Z Y: Charge p P ℂ): Prop where
   cost (i j:A): Like R.primary.full R.primary (rate R y) (fun _=> Z.table i j) (fun _=>Y.table i j) (fun k _=> R.primary.length k ^ (m i-m j-1))
   shape (i j:A): Shape (Y.table i j) (1+m j-m i)

lemma Criteria.read {Z Y: Charge p P ℂ} (r: Criteria R m y Z Y) (H : ∀ i, R.window i=Ici (R.beg i))
    {i j:A} {d :ℕ} (hh : (d:ℤ)≤ 1+m j-m i) (hy : 0<y) [Nonempty ι] (q:P) :
    reading d (fun t:ℝ=>Z.table i j (t • q))= if 1+m j-m i=d then Y.table i j q else 0:= by
   have ht : weak (m i-m j-1) y d:= by
      unfold weak; push_cast; have hx : (d:ℝ)≤ 1+(m j:ℝ)-m i:= by exact_mod_cast hh
      linarith
   rw [rangle ((r.cost i j).lat.smooth (R.start (Classical.arbitrary ι))), ←(r.shape i j).stage']; unfold stage Tensor.diagonal Tensor.coeff; rw [zero_charge H (r.cost i j) ht]

/-- One piece of `$Q E$`. Use lower-dimensional tested jets disappearing; no claim for higher dimensions. -/
private lemma take_product {Z Y: Charge p P ℂ} (r: Criteria R m y Z Y) (H : ∀ i, R.window i=Ici (R.beg i)) (hy : 0<y) [Nonempty ι]
    {i j:A} (q:P) (x u:ℤ) (d:ℕ) {M : ℝ→ℝ→ℂ} (hM : ∀ t, ContDiff ℝ ∞ (M t)) {c : ℂ} (h : m i+x+d = (u:ℤ)+1)
    (hl : ∀ j':ℕ, m j+x+j' ≤ u → Tendsto (fun t=> reading j' (M t)) atTop (𝓝 (if m j+x+j'=u then c else 0)))
    (hs : u<m j+x → c=0) : Tendsto (fun t=> reading d (fun w:ℝ=> Z.table i j (w • q)*M t w)) atTop (𝓝 (Y.table i j q*c)) := by
    have hz : ContDiff ℝ ∞ fun w:ℝ=> Z.table i j (w • q):= ((r.cost i j).lat.smooth (R.start (Classical.arbitrary ι))).comp (by fun_prop : ContDiff ℝ ∞ fun w:ℝ=>w • q)
    simp_rw [read_mul (g:=M _) hz (hM _)]
    let ℓ : ℤ:=1+m j-m i
    let T (k:ℕ) := if (k:ℤ)=ℓ then Y.table i j q*c else 0
    let z (k:ℕ) := reading k fun w:ℝ=>Z.table i j (w • q)
    have hk : ∀ k∈ Finset.range (d+1), Tendsto (fun t=> z k*reading (d-k) (M t)) atTop (𝓝 (T k)) := by
       intro k hk; have he : k≤d:= by simp at hk; omega
       rcases lt_or_ge (k:ℤ) ℓ with h1|h1
       · have hz' : z k=0:= by dsimp only [z]; rw [r.read H h1.le hy, if_neg (by dsimp only [ℓ] at *; omega)]
         simp [hz',T,h1.ne]
       have hi : m j+x+(↑(d-k):ℤ)≤u:=by dsimp only [ℓ] at *; omega
       have hm := (hl (d-k) hi).const_mul (z k)
       rcases lt_or_eq_of_le h1 with hu|hu
       · have hv : m j+x+(↑(d-k):ℤ)<u:=by dsimp only [ℓ] at *; omega
         simpa [T,Ne.symm hu.ne,hv.ne] using hm
       dsimp only [ℓ] at hu
       have hv : m j+x+(↑(d-k):ℤ)=u:=by omega
       have he : z k=Y.table i j q:= (r.read H hu.ge hy q).trans (if_pos hu)
       simpa [T,hv,ℓ,he,hu] using hm
    have he := tendsto_finsetSum (Finset.range (d+1)) hk
    convert! he using 2 -- equality of nhds
    rcases lt_or_ge ℓ 0 with h1|h1
    · have hj : Y.table i j=0:= (r.shape i j).charge h1
      rw [hj,Pi.zero_apply,zero_mul]; symm; exact Finset.sum_eq_zero fun k hk=> if_neg (ωcheck h1)
    rcases lt_or_ge (d:ℤ) ℓ with h2|h2
    · have hv : c=0:=hs (by dsimp only [ℓ] at *; omega)
      simp [hv,T]
    rw [Finset.sum_eq_single ℓ.toNat (fun i0 _ h=> if_neg (by omega : (i0:ℤ)≠ℓ)) (fun hi=> by simp only [Finset.mem_range] at hi; omega)]; exact Eq.symm (if_pos (show (ℓ.toNat:ℤ)=ℓ by omega))
where
 ωcheck {w : ℤ} (he : w<0) {k:ℕ} : (k:ℤ)≠w:= by omega


variable [Fintype A]
private def Zout (Z:Charge p P ℂ) (M: ℝ→ Row A P ℂ) (t x : ℝ) : Slash A P ℂ:= fun l i k=> ∑ j:A, Z.table i.1 j (x • i.2)* M t (sail (ray (l++(j,i.2)::k)) x)
omit [NormedSpace ℝ P] [NormedAddCommGroup P] [NormedSpace ℝ E] [NormedAddCommGroup E] [Fintype A] in
lemma mark_visit (b p) {z : Mode A P→Mode A E} (hz : ∀ i,(z i).1=i.1) (w : Legs (Mode A P)) (F: Slash A E ℂ):
   visit b p (w.map z) F=visit b p w (fun l i k=> F (l.map z) (z i) (k.map z)) := by
   induction w generalizing F with
   | nil=> rfl
   | cons i w ih=> simp only [List.map_cons, visit_cons, ih,hz,List.map_nil]
private lemma path_visit (Z: Charge p P ℂ) (M : ℝ → Row A P ℂ) (t x : ℝ) (w : Legs (Mode A P)) :
   Z.raise (M t) (sail (ray w) x)=visit true p w (Zout Z M t x) := by
   simp_rw [visit_Z,ray_go]; rw [mark_visit] ;· unfold Zout; simp
   exact fun _=> rfl

/-- The Taylor limits of $Z E$, reading at engineering h+1. -/
theorem torch_limit {Z Y : Charge p P ℂ} (r : Criteria R m y Z Y) (H : ∀ i, R.window i=Set.Ici (R.beg i)) (hy : 0<y) [Nonempty ι] (M : ℝ→ Row A P ℂ) (F : Row A P ℂ) (u : ℤ)
   {w : Legs (Mode A P)} (hw : Course b w) (d : ℕ) (hd : fieldDim m w + d=u+1)
   (hM : ∀ w' : Legs (Mode A P), Course b w' → w'.length=w.length → ∀ t, ContDiff ℝ ∞ (fieldVal (M t) (ray w'))) (hs : Form F m u b)
   (hl : ∀ w' : Legs (Mode A P), Course b w' → w'.length=w.length → ∀ j:ℕ, fieldDim m w'+j≤u → Tendsto (fun t=> torch j (M t) w') atTop (𝓝 (if fieldDim m w'+j=u then F w' else 0))) :
   Tendsto (fun t=> torch d (Z.raise (M t)) w) atTop (𝓝 (Y.raise F w)):= by
   have Hz (i : Mode A P) (j : A) : ContDiff ℝ ∞ fun x:ℝ=> Z.table i.1 j (x • i.2):= ((r.cost i.1 j).lat.smooth (R.start (Classical.arbitrary ι))).comp (by fun_prop : ContDiff ℝ ∞ fun x:ℝ=> x • i.2)
   have H1 l i k (h:l++i::k=w) t (j:A) : ContDiff ℝ ∞ fun x:ℝ=> M t (sail (ray (l++(j,(i: Mode A P).2)::k)) x):= hM _ (visit_course b l k i (by rw [h]; exact hw) j) (by simp [← h]) t
   simp_rw [torch_at, path_visit]; rw [visit_Z Y]
   have hx t l i k (h:l++i::k=w): ContDiff ℝ ∞ (fun x=> Zout Z M t x l i k):= ContDiff.sum (fun j _=> (Hz i j).mul (H1 l i k h t j))
   simp_rw [visit_read (hx _)]
   refine visit_limit (fun l i k h=> ?_)
   unfold Zout; have he t j:= (Hz i j).mul (H1 l i k h t j)
   simp_rw [read_sum (fun j _=> he _ j)] -- param?
   refine tendsto_finsetSum Finset.univ (fun j he=>?_)
   let X:=l++(j,i.2)::k; have h' : Course b X:= visit_course b l k i (by rw [h]; exact hw) j
   have hX : fieldDim m X=fieldDim m w-m i.1+m j := by rw [← h]; exact visit_field ..
   have HX:=hl X h' (by simp [X,← h])
   refine take_product r H hy i.2 (fieldDim m w-m i.1) u d (fun t=> H1 l i k h t j) (by omega) (fun j' ht=> ?_) ?_
   · specialize HX j' (by omega); rw [hX, add_comm (fieldDim m w-m i.1)] at HX; exact HX
   intro hi; have hj : u-fieldDim m (ray X)<0:= by rw [ray_dim]; omega
   have hu := (hs ℝ _ (ray_course h')).charge hj
   exact Eq.trans (congr_arg F (ray_sail X).symm) (congr_fun hu 1)
end Charge
end YM.MS.Plane
