import YM.MSbar.Counter.Region
/-! Fits analytic after multiplying by enough powers, pointwise with a *uniform* Laurent depth
on the entire region. This includes UV singularity at each finite order (operators &
counterterms), not radial loops after continuation (which preserve analytic budget). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Counter
open Dim Symbol Domain Diagram Scale Super Loops Function Set Filter
open scoped Classical Topology BigOperators ContDiff
variable {C:Type} {i m j t:ℕ} {U V:Set ℂ} {W:Edition C}{d:Bit} {f g: Vertex C}{F G:Functionals C}

def swell {X:Type*} [SMul ℂ X](i:ℕ): (ℂ→X)→ℂ→X:= times fun z=> z^i
lemma swell_inner {E:Type*}[SMul ℂ E](F:ℂ→E)(z:ℂ): swell i F z=z^i• F z:=rfl
@[simp] lemma bare_swell {E:Type*}[MulAction ℂ E](F:ℂ→E): swell 0 F= F:= funext fun z=> by simp [swell_inner]
lemma thread {E:Type*}[MulAction ℂ E](F:ℂ→E): swell i (swell j F)= swell (i+j) F:= funext fun z=> by rw [swell_inner,swell_inner,swell_inner,pow_add,mul_smul]
def Price (i:ℕ) (U:Set ℂ) (W:Edition C)(d:Bit)(F:Functionals C):Prop := ∃ G:Functionals C, Bright U W d G ∧ EqOn (swell i F) G (rim U)
-- avoid Transfer.Market conflict
abbrev Fits (U:Set ℂ) (W:Edition C)(d:Bit)(F:Functionals C):Prop:= ∃ m,Price m U W d F
abbrev Regular (U:Set ℂ)(W:Edition C)(d:Bit) := Price 0 U W d
lemma Bright.regular (h: Bright U W d F): Regular U W d F:= ⟨F,h,by rw [bare_swell]; intro _ _; rfl⟩
lemma cold (hf: Live W d f): Bright U W d (liftV f):= Full.shrink hf (subset_univ _)
namespace Price
lemma rem (h:Regular U W d F): ∃ G, Bright U W d G ∧ EqOn F G (rim U):= by simpa only [Price,bare_swell] using (h:Price 0 U W d F)
lemma recognize (h:Price i U W d F) (H:EqOn G F (rim U)): Price i U W d G := by
    obtain ⟨f,hf,he⟩:= h; exact ⟨f,hf,EqOn.trans (fun x hx=> congr_arg ((x^i:ℂ) • ·) (H hx)) he⟩
lemma add (h:Price i U W d F) (hp:Price i U W d G): Price i U W d (F+G):= by
    obtain ⟨X,hX,h1⟩:=h;obtain ⟨Y,hY,h2⟩:=hp; exact ⟨X+Y,hX.add hY,fun x hx=> by rw [Pi.add_apply,← h1 hx,← h2 hx]; simp [swell_inner]⟩
lemma sub (h:Price i U W d F) (hp:Price i U W d G): Price i U W d (F-G):= by
    obtain ⟨X,hX,h1⟩:=h;obtain ⟨Y,hY,h2⟩:=hp; exact ⟨X-Y,hX.sub hY,fun x hx=> by rw [Pi.sub_apply,← h1 hx,← h2 hx]; simp [swell_inner,smul_sub]⟩
lemma zero : Price i U W d 0:= ⟨0,Full.zero .., fun x hx=> by simp [swell_inner]⟩
lemma scale (h:Price i U W d F) (c:ℂ): Price i U W d (c•F) := by
    obtain ⟨G,hG,hx⟩:=h; exact ⟨c•G,hG.scale c, fun x hv=> by rw [Pi.smul_apply,← hx hv,swell_inner,swell_inner, Pi.smul_apply,smul_comm]⟩
lemma sum {ι:Type*} {A:ι→Functionals C}(s:Finset ι)(h:∀ x∈s,Price i U W d (A x)) : Price i U W d (∑ x∈s,A x):=by induction s using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i s he ih=> rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma slim (h:Price i U W d F) (hw:V⊆U): Price i V W d F:= by
    obtain ⟨G,hG,h⟩:=h; exact ⟨G,hG.shrink hw,fun z hz=> h (show z∈rim U from ⟨hw hz.1,hz.2⟩)⟩
lemma alive (h:Price i U W d F){z:ℂ} (hz:z∈rim U): Live W d (F z):=by
    obtain ⟨G,hG,h⟩:=h; have he : (z^i)⁻¹ • G z= F z:= by rw [← h hz,swell_inner,inv_smul_smul₀ (pow_ne_zero _ (show z≠0 from hz.2))]
    rw [← he]; exact Live.scale _ (hG.freeze hz.1)
variable [p: Profit U]
lemma grow (h:Price i U W d F)(he: i≤j):Price j U W d F:= by
    obtain ⟨k,rfl⟩:= Nat.exists_eq_add_of_le he
    obtain ⟨F,hF,H⟩:=h
    exact ⟨swell k F, Bright.temp hF (differentiableOn_id.pow _), by rw [add_comm,← thread]; exact fun z hz=>congr_arg ((z^k:ℂ) • ·) (H hz)⟩
lemma unit (h:Price i U W d F){p:ℂ→ℂ}(hp:DifferentiableOn ℂ p U): Price i U W d (times p F):= by
    obtain ⟨G,hG,H⟩:=h; exact ⟨times p G,Bright.temp hG hp,fun z hz=> by simp only [times,← H hz,swell_inner,smul_comm (z^i) (p z)]⟩
include p in -- needed isOpen, inference?
lemma clears (h:Price i U W d F): Bright (rim U) W d F := by
    have hv:IsOpen (rim U):= p.pub.sdiff isClosed_singleton
    obtain ⟨G,hG,h⟩:= h; let f(z:ℂ):=(z^i)⁻¹
    have hl := hG.shrink (show rim U⊆ U from sdiff_subset); have hm:DifferentiableOn ℂ f (rim U):= fun x hx=> (differentiableWithinAt_id.pow i).inv (pow_ne_zero _ (show x≠0 from hx.2))
    have he z (hz:z∈ rim U): f z • G z= F z:=by rw [← h hz, swell_inner]; exact inv_smul_smul₀ (pow_ne_zero _ (show z≠0 from hz.2)) _
    apply Full.congr (F:=times f G) ?_ hv he; apply using_cell (fun z hz=> live_cell (Live.scale _ (hl.freeze hz))); intro E i1 i2 i3 m x hx
    exact ⟨(Symbol.AH.holomorphic (X:=E) hv hm).mul ((hl.licensed.ev _ _ hx).cost), fun H=> (p.proper (eq_univ_of_univ_subset (H ▸ (show rim U ⊆ U from sdiff_subset)))).elim⟩
end Price
end YM.MSbar.Counter
