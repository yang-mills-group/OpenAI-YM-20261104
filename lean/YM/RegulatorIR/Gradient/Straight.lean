import YM.RegulatorIR.Gradient.Linear

/-! `Draft` is the rank-diagonal term of the full Ward substitution, not a
new field identity. This lemma includes localized (absolute) cover inputs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Train Uniform Diagram Function Finset
open scoped ENNReal Topology BigOperators Classical
variable {X Y Z:Type}{r:ℕ}

lemma cut_uses (Γ:Curve X Y)(T:Packet X r)(g:Fin r→ℕ){s}(h:charge g=s)(t:Fin (r+charge g)≃Fin (r+s))(y:Tuple Y (r+s)) :
    cut Γ T s g y= symmetry (series Γ g T) (y ∘ t):=by subst s; rw [cut,dif_pos rfl]; exact (Packet.is_symmetry (series Γ g T) t y).symm
lemma symm_transport {m n:ℕ}{T:Packet X m}{Q:Packet X n}(h:m=n)(f:Fin m≃Fin n)(H:∀ z:Tuple X n,T (z∘f)=Q z)(x:Tuple X n) : symmetry T (x∘f)=symmetry Q x:=by
 subst n; rw [Packet.is_symmetry,symmetry_at,symmetry_at]; apply congr_arg
 have he : (∑ a : Equiv.Perm (Fin m),Q (x ∘ a))=∑ a:Equiv.Perm (Fin m), T (x ∘  ⇑(a*f)):=Finset.sum_congr rfl fun _ _=> (H _).symm
 rw [he]; exact (Equiv.sum_comp (Equiv.mulRight f) (fun u=> T (x∘u))).symm

variable (p:X↪Z)(q:Y↪Z)(K:Layer Z Z)

def diagonal (Γ:Curve X Y): Prop := ∀ i (v: Tuple Y 1), Γ i 0 v=K (q (v 0)) (p i)

lemma carriage (T:Packet X r) {Γ:Curve X Y}(hc: diagonal p q K Γ){B:ℝ≥0∞} (ht: quota T 1≠ ⊤)(hw:height K B)(hB:B≠⊤) :
   updateQ Γ T 0=crop q (draft K (offer p T)) := by
 let g:Fin r→ℕ:=0
 have he : turns r 0={g}:= by ext i; rw [turns_iff, entryZero, mem_singleton]
 let S:=series Γ g T
 let V:= drawing (offer p T) K (List.finRange r)
 have hN:= (entryZero g).mpr rfl
 let J:((i:Fin r)×Fin (g i+1)) ≃ Fin r := Equiv.ofBijective (fun u=>u.fst) ⟨?_,fun x=> ⟨⟨x,0⟩, rfl⟩⟩
 let e :Fin (r+charge g) ≃ Fin r:=(stations g).symm.trans J
 have hp:quota (offer p T) 1 ≠ ⊤:= ne_top_of_le_ne_top ht (Stalk.quota_collect _ _ _)
 unfold updateQ; rw [he, sum_singleton]
 have hS (z:Tuple Y r): S (z∘e)=crop q V z:=by
    unfold S crop; rw [Function.comp_apply]; unfold V; rw [ray_full _ _ _ hw hp hB]
    unfold series
    rw [← (injectT p).tsum_eq]; apply tsum_congr; intro x; rw [offer_eq]; apply congr_arg
    unfold tracked trips; apply Finset.prod_congr rfl;intro i _; change Γ _ 0 (_:Tuple Y _) = _; rw [hc]
    apply congr_arg (K · (p (x i)))
    apply congr_arg q
    -- e cancels
    change z (e (stations g ⟨i,0⟩)) = z i
    unfold e; rw [Equiv.trans_apply, Equiv.symm_apply_apply]; rfl
    intro x hx; by_contra! h; apply hx; change offer _ _ _ * _ = 0; rw [offer_zero _ h,zero_mul]
 ext1 y; rw [cut_uses Γ T g hN e, symm_transport (T:=series Γ g T) (by omega) e hS]; change symmetry (crop q V) y=symmetry V (acrossT q y); rw [symmetry_at,symmetry_at]; rfl
 rintro ⟨x,i⟩ ⟨y,j⟩ he; change x=y at he; subst y; congr!; exact Subsingleton.elim (α:=Fin 1) ..
end YM.RegulatorIR.Gradient
