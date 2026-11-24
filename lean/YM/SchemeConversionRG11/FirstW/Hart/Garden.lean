import YM.SchemeConversionRG11.FirstW.Hart.Franc
/-! Discrete polynomial approximation through requested finite Taylor order.
Newton bounds on moving Manhattan region (upper representation available pre-on-shell). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Lattice Pert Align Topology Set Metric Submodule
open Laurent (size)
open scoped BigOperators Classical
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma tailOp (h : ℕ) (p:Cover→E) (D : List Axis) (hd : D.length≤h) :
  combine D (MultiNext.SignedSource.Newt.tail h p) = MultiNext.SignedSource.Newt.tail (h-D.length) (combine D p) := by
  induction D generalizing h p with
  | nil=> simp [combine]
  | cons i t ih=>
    cases h with
    | zero=> simp at hd
    | succ h=>
      rw [combine,←combine_up,combine,←combine_up,show up i (MultiNext.SignedSource.Newt.tail (h+1) p)=_ from MultiNext.SignedSource.Newt.currency h p i];
      rw [List.length_cons,Nat.add_sub_add_right]; exact ih _ (up i p) (by simpa using hd)
lemma scalp (D : List Axis) (p : Cover→E) (h : ℕ)(hd:D.length<h) : combine D (MultiNext.SignedSource.Newt.take h p) 0=combine D p 0 := by
  have he:=congrFun (tailOp h p D hd.le) 0; have hp (h p) : MultiNext.SignedSource.Newt.tail h p = p-MultiNext.SignedSource.Newt.take h (p:Cover→E) := rfl
  rw [hp h p,combine_sub] at he
  obtain ⟨b,hb⟩:=Nat.exists_eq_add_one.mpr (Nat.sub_pos_of_lt hd); rw [hb,MultiNext.SignedSource.Newt.top] at he
  exact (sub_eq_zero.mp he).symm
variable {G : Gauge} {T : Itinerary} {k : ℕ} {r C : ℝ}
-- use cover Manhattan radius from baseline
def Warrant (T : Itinerary) (r : ℝ) (k : ℕ) (W : ℕ→Field4 G) := ∃ C>0,∀ᶠ i in atTop, ∀ (a:Axis)(D:List Axis), D.length=k+1 → ∀ x:Cover,T.gap i*(size x:ℝ)≤r → ‖combine D (field4 a (W i)) x‖ ≤ C*T.gap i^(k+2)
def Messed (T : Itinerary) (r : ℝ) (k : ℕ) (W : ℕ→Field4 G) := ∃ C>0,∀ᶠ i in atTop, ∀ (a:Axis)(D:List Axis), D.length ≤ k+1 → ∀ x:Cover,T.gap i*(size x:ℝ)≤r →
  ‖combine D (field4 a (W i)) x‖ ≤ C*T.gap i^(k+2)*(1+(size x:ℝ))^(k+1-D.length)
def allotR (k) (W : Field4 G) (x : Edge Cover) := MultiNext.SignedSource.Newt.take (k+1) (field4 x.2 W) x.1
def planR (k : ℕ) (W : Field4 G) : stor G k := ⟨allotR k W, stor_mem.mpr (fun i=>by change MultiNext.SignedSource.Newt.take (k+1) (field4 i W) ∈ Loft G.Color k; exact loft_adapt _ (field4 i W))⟩
variable (W : ℕ→Field4 G)
lemma initial_warrant (hp : Warrant T r k W) : Messed T r k (fun i=> W i - (planR k (W i)).val) := by
  obtain ⟨C,hC,H⟩:=hp; refine ⟨C,hC,H.mono fun i hi a D hd x hx=>?_⟩
  have hm : 0 ≤ C*T.gap i^(k+2) := by have ht:=T.positive i; positivity
  let f:= field4 a (W i)
  let j:= k+1-D.length
  change ‖combine D (MultiNext.SignedSource.Newt.tail (k+1) f) x‖≤_
  rw [tailOp _ f D hd]; refine MultiNext.SignedSource.Newt.localized j hm (r/T.gap i) ?_ _ ((le_div_iff₀ (T.positive i)).mpr (by rw [mul_comm]; exact hx)) -- mul comm placeholder
  intro l hl x hx; rw [switch_order, ←append_op]; refine hi _ _ (by rw [List.length_append,hl]; unfold j; omega) _ ?_; rw [mul_comm]; exact (le_div_iff₀ (T.positive i)).mp hx
lemma plus_field (f g:ℕ→Field4 G) (h:Messed T r k f)(he:Messed T r k g): Messed T r k (fun i=> f i+g i) := by
  obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,J⟩:=he; refine ⟨C+D,add_pos hC hD,(H.and J).mono fun i hi j l hl x hx=>?_⟩
  rw [show field4 j (f i+g i)=field4 j (f i)+field4 j (g i) from rfl,combine_add,Pi.add_apply]; exact ((norm_add_le ..).trans (add_le_add (hi.1 j l hl x hx) (hi.2 j l hl x hx))).trans (le_of_eq (by ring))
lemma Messed.known (p : ℕ→Field4 G) (hr : 0 < r) (h : Messed T r k p) (x : Edge Cover) : ∃ C:ℝ,0<C∧∀ᶠ i in atTop, ‖(T.gap i^(k+2))⁻¹ • p i x‖ ≤ C := by
  obtain ⟨C,hC,H⟩:=h
  let q := (size x.1:ℝ); refine ⟨C*(1+q)^(k+1),by unfold q; positivity,?_⟩
  filter_upwards [H,(T.cutoff.mul_const q).eventually (ge_mem_nhds (lt_of_eq_of_lt (zero_mul _) hr))] with i hi he
  have hp:=pow_pos (T.positive i) (k+2); have hu:= hi x.2 [] (by simp) x.1 he; change ‖p i x‖ ≤ C*T.gap i^(k+2)*(1+q)^(k+1) at hu; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le, inv_mul_le_iff₀ hp]; linarith only [hu]
lemma graded_pay (W : stor G k) (l j : ℕ) (ha : l+j=k) (D:List Axis) (hp:D.length=l) (a : Axis) : ∃ C:ℝ,0<C∧∀ x:Cover,‖combine D (field4 a W.val) x‖≤ C*(1+(size x:ℝ))^j := by
  have he : combine D (field4 a W.val)∈Loft G.Color j := loft_scoped _ _ _ (show _ from (show field4 a W.val ∈ _ from (show j+l=k from by omega) ▸ stor_mem.mp W.property a)) _ hp -- subst
  obtain ⟨C,hc,H⟩:=loft_scale j he
  refine ⟨C,hc,fun x=> le_trans (H x) ?_⟩; unfold stepY; gcongr; exact yard_size x
lemma lump_eval (W : stor G k) : ∃ C>0,∀ a:Axis,∀ D:List Axis,D.length≤k+1 → ∀ x:Cover,
     ‖combine D (field4 a W.val) x‖ ≤ C * (1+(size x:ℝ))^(k+1-D.length) := by
  have e (D : List Axis) (a : Axis) : ∃ C>0,∀ x:Cover, ‖combine D (field4 a W.val) x‖ ≤ C * (1+(size x:ℝ))^(k+1-D.length) := by
    by_cases h:D.length≤k; swap
    · exact ⟨1,by norm_num, fun x=> by rw [combine_top (stor_mem.mp W.property a) _ (lt_of_not_ge h)]; change ‖(0:G.Color)‖≤_; rw [norm_zero]; positivity⟩
    obtain ⟨C,hC,H⟩:=graded_pay W D.length (k-D.length) (by omega) D rfl a
    exact ⟨C,hC,fun x=>le_trans (H x) (by gcongr; simp; omega)⟩
  choose J hJ H using e; let P (v : Axis× Trad (k+1)) := J (List.ofFn v.2.2) v.1
  let C:=1+∑ v,P v; refine ⟨C,add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun i _=>(hJ ..).le)), fun a D h x=> ?_⟩
  obtain ⟨t,ht⟩:=lists D h; rw [← ht]; refine le_trans (H _ _ x) (mul_le_mul_of_nonneg_right ?_ (by positivity)); exact (Finset.single_le_sum (f:=P) (fun i _=>(hJ ..).le) (Finset.mem_univ (a,t))).trans (le_add_of_nonneg_left zero_le_one)
end YM.RG11.FirstW
