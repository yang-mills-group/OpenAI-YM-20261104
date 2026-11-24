import YM.MSbar.Transfer.Vanishing

/-! Growth estimator for dimension transfer on continuum *fixed-op* identity, stable under
successive Mellin analytic integrations. Choose wide halfplanes r∈[1,∞). No assertion here on
combined *bare momentum* graph loops (they need continuation to the right in ε, i.e. left in s).
Use this only on shell and exact identity integrals with UV decay. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Transfer
open Complex Metric Filter Set MeasureTheory Function
open Dim.Dual
open scoped Topology ContDiff BigOperators Classical
variable {k j n m : ℕ} {f g : ℂ→ℂ} {z : ℂ} {C T D : ℝ}

def toll (j m n : ℕ) (c : ℝ) (z : ℂ) := c * ‖Γ z‖^j * Real.exp (m*z.re) * ‖z‖^n
lemma toll_nn (hc : 0≤C): 0 ≤ toll j m n C z := by unfold toll; positivity
lemma toll_mono (h : 1 ≤ z.re) (hc : 0 ≤ C) {m' n'} (hm : m≤m') (hn : n≤n') (H:C≤D) : toll j m n C z ≤ toll j m' n' D z := by
   have hE:1 ≤ ‖z‖:= h.trans (Complex.re_le_norm _); have hz : 0≤z.re:=zero_le_one.trans h
   have hD:=hc.trans H; unfold toll; gcongr
lemma product : toll j m n C z*toll k m n D z=toll (j+k) (2*m) (2*n) (C*D) z:=by
    unfold toll; simp only [two_mul,Nat.cast_add,add_mul,Real.exp_add,pow_add]; ring
lemma pay_add : toll j m n C z+toll j m n D z=toll j m n (C+D) z:=by unfold toll; ring
lemma pay_rate (p:ℝ) : p*toll j m n C z=toll j m n (p*C) z:=by unfold toll; ring

-- compact param control of toll. Different sets restrict by monotonicity later
set_option linter.unusedSectionVars false
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
structure Centered (j:ℕ)(F : ℂ×X→ℂ)(K : Set X): Prop where
    result : ∃ T:ℝ,∃ C:ℝ,∃ m n,0≤C ∧ ∀ z:ℂ,T ≤ z.re →∀ x∈K, ‖F (z,x)‖ ≤ toll j m n C z
variable {F G : ℂ×X→ℂ} {K:Set X}
namespace Centered
lemma books (h : Centered j F K)(A : ℝ) : ∃ T C:ℝ,A ≤ T ∧ 0≤C∧ ∃ m n,∀ z:ℂ,T≤z.re→ ∀ x∈K,‖F (z,x)‖≤ toll j m n C z:=by
    obtain ⟨⟨d,D,m,n,hD,h⟩⟩:=h; exact ⟨max A d,D,le_max_left ..,hD,m,n,fun z hz=> h z ((le_max_right ..).trans hz)⟩
lemma share (h : Centered j F K)(H:Centered k G K) (A : ℝ):∃ T C:ℝ,A≤T∧0≤C∧∃ m n,∀ z:ℂ,T ≤ z.re→∀ x∈K, ‖F (z,x)‖≤toll j m n C z ∧ ‖G (z,x)‖≤ toll k m n C z:=by
    obtain ⟨T,C,hp,hC,m,n,h⟩:=h.books (max A 1)
    obtain ⟨u,D,hq,hD,m',n',H⟩:=H.books T
    refine ⟨u,max C D,le_trans ((le_max_left ..).trans hp) hq,hC.trans (le_max_left ..),max m m',max n n',fun z hz x hx=>?_⟩
    have hB:=hq.trans hz; have hz':1 ≤ z.re:= le_trans ((le_max_right ..).trans hp) hB
    exact ⟨(h z hB x hx).trans (toll_mono hz' hC (le_max_left ..) (le_max_left ..) (le_max_left ..)),(H z hz x hx).trans (toll_mono hz' hD (le_max_right ..) (le_max_right ..) (le_max_right ..))⟩
lemma add (h : Centered j F K)(H: Centered j G K) : Centered j (F+G) K:= by
    obtain ⟨t,C,ht,hC,m,n,hB⟩:= h.share H 1; refine ⟨t,C+C,m,n,add_nonneg hC hC,fun z hz x hx=>?_⟩ -- syntax
    obtain ⟨hL,hR⟩:=hB z hz x hx; rw [← pay_add]; exact (norm_add_le ..).trans (add_le_add hL hR)
lemma neg (h:Centered j F K) : Centered j (-F) K:=⟨by obtain ⟨⟨T,C,m,n,hC,h⟩⟩:=h; exact ⟨T,C,m,n,hC,fun z hz x hx=>by rw [Pi.neg_apply,norm_neg]; exact h z hz x hx⟩⟩
lemma sub (h : Centered j F K)(H: Centered j G K) : Centered j (F-G) K:= by rw [sub_eq_add_neg]; exact h.add H.neg
lemma mul (h : Centered j F K)(H : Centered k G K): Centered (j+k) (F*G) K:=by
    obtain ⟨t,C,ht,hC,m,n,hB⟩:=h.share H 1; refine ⟨t,C*C,2*m,2*n,mul_nonneg hC hC,fun z hz x hx=>?_⟩
    rw [← product,Pi.mul_apply,norm_mul]; obtain ⟨hL,hR⟩:=hB z hz x hx; exact mul_le_mul hL hR (norm_nonneg _) (toll_nn hC)
lemma no_z {f:X→ℂ} (h:∀ x∈K,‖f x‖≤C) : Centered 0 (fun p=> f p.2) K:=⟨1,max C 0,0,0,le_max_right ..,fun z _ x hx=> by simpa [toll] using (h x hx).trans (le_max_left C 0)⟩
lemma arg : Centered 0 (fun x:ℂ×X=>x.1) K:=⟨1,1,0,1,zero_le_one,fun z _ x _=> by simp [toll]⟩
lemma zero : Centered j (fun (_:ℂ×X)=>0) K:=⟨0,0,0,0,le_rfl,fun _ _ _ _=> by simp [toll]⟩
lemma mono (h:Centered j F K) {K'} (he: K' ⊆ K) : Centered j F K':=⟨by obtain ⟨t,C,_,hp,m,n,h⟩:=h.books 0; exact ⟨t,C,m,n,hp,fun z hz x hx=> h z hz x (he hx)⟩⟩
lemma comp (h:Centered j F K) (k:Y→X){S:Set Y} (he:MapsTo k S K) : Centered j (fun x:ℂ×Y=> F (x.1,k x.2)) S:=⟨by obtain ⟨t,C,_,hp,m,n,h⟩:=h.books 0; exact ⟨t,C,m,n,hp,fun z hz x hx=>h z hz _ (he hx)⟩⟩
end Centered
set_option linter.unusedSectionVars false
-- normalized market global uptake for composing on symbols; only proof component, no analyticity fields included
def Market (j:ℕ)(F : ℂ×X→ℂ):Prop:=∀ K:Set X,IsCompact K→ Centered j F K
namespace Market
lemma add (h:Market j F)(H:Market j G): Market j (F+G):= fun K hc=>(h K hc).add (H K hc)
lemma neg (h:Market j F): Market j (-F):= fun K hc=>(h K hc).neg
lemma sub (h:Market j F)(H:Market j G): Market j (F-G):= by rw [sub_eq_add_neg]; exact h.add H.neg
lemma mul (h:Market j F)(H:Market k G): Market (j+k) (F*G):= fun K hc=>(h K hc).mul (H K hc)
lemma comp (h:Market j F) {g:Y→X}(hg:Continuous g) : Market j (fun x:ℂ × Y=> F (x.1,g x.2)):= fun K hK=>(h _ (hK.image hg)).comp g (mapsTo_image _ _)
lemma no_z {f:X→ℂ}(hf:Continuous f): Market 0 (fun p:ℂ×X=>f p.2):= by intro K hk; obtain ⟨C,H⟩:= hk.exists_bound_of_continuousOn hf.continuousOn; exact Centered.no_z H
lemma z_self : Market 0 (fun p:ℂ×X=>p.1) := fun _ _=> Centered.arg
lemma zero : Market j (0:ℂ×X→ℂ):= fun _ _=> Centered.zero
lemma sum {ι:Type*}{F:ι→ℂ×X→ℂ}{W:Finset ι}(h:∀ i∈W,Market j (F i)): Market j (∑ i∈W,F i):= by induction W using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact Market.zero | insert i W hw ih=> rw [Finset.sum_insert hw]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
end Market
end YM.MSbar.Transfer
