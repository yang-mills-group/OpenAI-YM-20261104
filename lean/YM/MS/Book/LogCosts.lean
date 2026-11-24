import YM.MS.Book.LogPS
import YM.MS.Book.Merit

/-!
# Polynomial log-independence for rent on `T→`

Choose power inside true multiplicative units at λ. Because of all-orders uniform
 support issue for tests, prove when symbols have cut in rank through each endpoint.
 `Ticket` etc. Action needed also on real-stence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Cylinder Lab Plane Convolve Logarithm
open PowerSeries (coeff)
variable {I A B : Type} [Fintype A][DecidableEq A] {p:Sector A}
variable {E:Type}[AddCommGroup E][Module ℝ E]{c:ℝ→ℂ}

-- Does lean synthesize Module ℝ (Cyl _ ℂ) ?
lemma pc_ready (hc:Decent c){f:ℝ→ Cyl B ℂ}(h:Ready f): Ready (fun x=> c x • f x):= by obtain ⟨v,hv,rfl⟩:=hc; convert (Ready.smul hv h) using 1; rfl
lemma value_sum {F:I→ℝ→ E}(s:Finset I)(h:∀ i∈s,Ready (F i)): Ready (fun x=>∑ i∈s,F i x):= by convert Ready.sums s h using 1; ext; rw [Finset.sum_apply]
lemma substituted {v:ℝ→T (Cyl B ℂ)}{c:ℝ→Cn}(h:Ren c)(hs:∀ j,Ready fun x=>v x j) (i:ℕ): Ready (fun x=>substitute (c x) (v x) i):= by
    simp_rw [rules]; refine value_sum _ (fun j _=>pc_ready (h.pow j i) (hs j)) -- h.pow j returns Ren etc

variable (r:B→A)
-- restrict to a word in Branch only

def tagged (w:List A)(r:B→A): Cyl B ℂ→ₗ[ℂ] Cyl B ℂ where
    toFun F := ⟨fun l=>if l.map r=w then F.val l else 0,by obtain ⟨s,hs⟩:= fromCyl F; exact packed (s:=s) (fun l i hi h=>by split; exact hs l i hi h; rfl)⟩
    map_add' U V:= by apply Subtype.ext; funext l; by_cases he:l.map r=w <;> simp only; -- inspect
                       all_goals simp [he]
    map_smul' c F:= by apply Subtype.ext; funext l; by_cases he:l.map r=w <;> simp [he]

-- estimate finite lengths
lemma register (h:ℕ) : ∃ s:Finset (List A), ∀ l,l∈s↔ l.length≤h := by
   induction h with
   | zero=> exact ⟨{[]},fun _=> by simp⟩
   | succ n ih=>
      obtain ⟨s,hs⟩:=ih; let t:Finset (List A):= insert [] (Finset.univ.biUnion fun i:A=>s.image (List.cons i))
      refine ⟨t,fun l=>?_⟩; cases l with| nil=>simp [t]| cons i l=>simp [t,hs]
lemma trained (U:A→ℝ→Cn)(h:∀ i,Ren (U i)) (F: ℝ→ Cyl B ℂ)(hp: Ready F)(n k:ℕ)(hv:∀ x,Limit (F x).val n): Ready (fun x=>train (fun i=>U (r i) x) k (F x)):= by
    obtain ⟨s,hs⟩:=register (A:=A) n; let X (w:List A)(v:ℝ):= coeff k (w.map fun j=>U j v).prod; have he (x:ℝ): train (fun i=> U (r i) x) k (F x)=∑ w∈s,X w x • tagged w r (F x):= by
        apply Subtype.ext; ext l; by_cases hl:l.length≤n; swap
        · have hh := hv x l (by omega); simp [train_v,offer,tagged,hh]
        rw [train_v,sum_stack,Finset.sum_apply,Finset.sum_eq_single (l.map r)];
        · simp [Function.comp_def,X,offer,tagged]
        · intro w hw hx; simp [tagged,hx.symm]
        exact fun h=> (h ((hs _).mpr (by simpa using hl))).elim
    simp_rw [he]; exact value_sum _ (fun i _=> pc_ready (f:=fun x=>tagged i r (F x)) (c:=X i) (Ren.swath U h i k) (hp.linear ((tagged i r).restrictScalars ℝ)))
end YM.MS.Book.Program
