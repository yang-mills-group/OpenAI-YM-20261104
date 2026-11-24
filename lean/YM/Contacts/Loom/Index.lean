import YM.Contacts.Loom.Wave
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
abbrev Shelf (E α F : ℕ→Type):Type:= ∀ i,α i→E i→F i
abbrev Lamp (E : ℕ→Type): Type:= ∀ i,E i→ℝ
abbrev Frame (α E:ℕ→Type):Type:= ∀ i, α i → E i
variable (N)
variable (x:Frame α E)
variable {a b:Shelf E α F} {P: Shelf E α V} {d:ℕ→ℝ}
def Arms (k:ℕ) (r:ℝ)(d:ℕ→ℝ)(f:Shelf E α F):Prop:= N.Funds (fun i b=> ∀ j:α i, Brush k b (d i) (f i j) (x i j)) r
abbrev Budget (k:ℕ)(r:ℝ)(f:Shelf E α F):= Arms N x k r 1 f
variable {N x}
namespace Arms
lemma reveal (h:Arms N x k p d a) (he: ∀ᶠ i in atTop, ∀ j, b i j=ᶠ[𝓝 (x i j)] a i j) (hp:p≤r)(ht:j≤k): Arms N x j r d b:= h.lift hp (he.mono fun i hi y _ h j=> ((h j).shimmy (hi j)).smaller ht)
lemma lo (h:Arms N x k p d a)(hp:p≤r)(ht:j≤k): Arms N x j r d a:= reveal h (Eventually.of_forall fun _ _=>.refl _ _) hp ht
lemma also (h:Arms N x k p d a)(he:∀ᶠ i in atTop, ∀ j, d i ≤ f i ∧ b i j=ᶠ[𝓝 (x i j)] a i j): Arms N x k p f b:= h.lift le_rfl (he.mono fun i hi y _ h j=> ((h j).climb le_rfl (hi j).1).shimmy (hi j).2)
lemma sum (h:Arms N x k p d a)(he:Arms N x k p d b): Arms N x k p d (a+b):= h.fold he (Eventually.of_forall fun i _ _ _ _ h hx j=> (h j).gathering (hx j))
lemma opp (h:Arms N x k p d a): Arms N x k p d (-a):= h.lift le_rfl (Eventually.of_forall fun i _ _ hx j=> (hx j).opposite)
lemma sub (h:Arms N x k p d a) (he: Arms N x k p d b): Arms N x k p d (a-b):= by rw [sub_eq_add_neg]; exact h.sum he.opp
lemma weighted (h: Arms N x k p d a) (he:N.Rush q f)(hx:p+q=r): Arms N x k r d (fun i j=> f i • a i j) := h.loft (f:=fun i=>‖f i‖) (absolute he) (Eventually.of_forall fun i y _ hv k=> (hv k).smul (f i)) (Eventually.of_forall fun i=> norm_nonneg _) hx
lemma scale (h: Arms N x k p d a) (r:ℝ): Arms N x k p d (r • a):= h.weighted (Rush.settle r) (add_zero _)
lemma project (W:∀ i:ℕ,F i→L[ℝ] V i)(h:Arms N x k p d a)(hp:N.Rush q (fun i=>‖W i‖))(hr:p+q=r): Arms N x k r d (fun i j=> W i ∘ a i j) := h.loft hp (Eventually.of_forall fun i _ _ hx j=> (hx j).report _ le_rfl) (Eventually.of_forall fun i=>norm_nonneg _) hr
lemma const (a: Frame α F)(hQ : N.Funds (fun i z=> ∀ j:α i, ‖a i j‖≤ z) p) (he:∀ᶠ i in atTop,0≤d i): Arms N x k p d (fun i j _=> a i j) := hQ.lift le_rfl (he.mono fun i hi _ _ hx j=> (Brush.certified (k:=k) hi _).climb (hx j) le_rfl) -- k shadow
lemma zero (h:∀ᶠ i in atTop,0≤d i): Arms (F:=F) N x k p d 0:= const (fun _ _=>0) (Funds.mk ⟨_, Rush.zero, Eventually.of_forall (fun i=> by simp) ⟩) h -- replace
lemma spoke {γ:Type}(s:Finset γ)(a:γ→Shelf E α F)(h:∀ᶠ i in atTop,0≤d i)(hp:∀ i∈s,Arms N x k p d (a i)): Arms N x k p d (∑ i∈s,a i):= by induction s using Finset.induction with|empty=> simpa using zero h|insert i s hi ih=> rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).sum (ih (fun i hk=> hp i (mem_insert_of_mem hk)))
lemma read (h:Arms N x k p d a)(hp:p<q): ∀ᶠ i in atTop,∀ j:α i, Brush k (N.pow q i) (d i) (a i j) (x i j) := h.meet (Eventually.of_forall fun i _ _ _ he h j=> (h j).climb he le_rfl) hp
lemma nail (h:Arms N x k p d a)(z:∀ i, γ i→α i): Arms N (fun i j=> x i (z i j)) k p d (fun i j=> a i (z i j)):= h.lift le_rfl (Eventually.of_forall fun i x _ hL j=> hL (z i j))
end Arms
namespace Budget
open Arms
set_option quotPrecheck false
local notation "α₁" => (Eventually.of_forall fun i:ℕ=>(show 0 ≤ (1:ℕ→ℝ) i from zero_le_one))
lemma const (a: Frame α F)(hQ : N.Funds (fun i z=> ∀ j:α i, ‖a i j‖≤z) p) : Budget N x k p (fun i j _=>a i j):= Arms.const a hQ α₁
lemma value (a : ∀ i,F i)(h:N.Rush p fun i=>‖a i‖): Budget N x k p (fun i _ _=> a i):= const (fun i _=> a i) ⟨_, h, Eventually.of_forall fun _ => ⟨norm_nonneg _, fun _=> le_rfl⟩⟩
lemma twins (h:Budget N x k p a)(B:∀ i,F i →L[ℝ] V i →L[ℝ] Y i)(hf: Budget N x k q P)(hg: N.Rush s fun i=> ‖B i‖)(he:p+q+s=r): Budget N x k r (fun i j u=> B i (a i j u) (P i j u)):= by
    obtain ⟨f,hf',H⟩:=h.cap; obtain ⟨g,hg',G⟩:=hf.cap; refine ⟨_,(hg.times (hf'.times hg' rfl) (by linarith)).bind ((1+(1+1):ℝ)^k),?_⟩; filter_upwards [H,G] with i hi hx using ⟨mul_nonneg (mul_nonneg (norm_nonneg (B i)) (mul_nonneg hi.1 hx.1)) (by positivity),fun j=> ((hi.2 j).twins (hx.2 j) _).trim⟩
lemma mul (a b:Shelf E α (fun _=>ℝ))(h:Budget N x k p a)(hx:Budget N x k q b)(hr:p+q=r): Budget N x k r (a*b):= h.twins (fun _=>ContinuousLinearMap.mul ℝ ℝ) hx (Rush.settle _) (by rw [hr, add_zero])
lemma zero : Budget (F:=F) N x k p 0:= Arms.zero α₁
lemma tally (f:ℕ→ℝ)(h:N.Rush p f): Budget N x k p (fun i _ _=> f i):= value f (absolute h)
lemma power {A:Shelf E α (fun _=>ℝ)} (h:Budget N x k p A)(j:ℕ): Budget N x k (p*j) (A^j):= by
   induction j with| zero=>simp only [pow_zero, Nat.cast_zero,mul_zero]; exact tally (fun _=>1) (Rush.settle 1)|succ j ih=> rw [pow_succ]; exact mul _ _ ih h (by push_cast; ring)
-- lift.F identity composed on xnormalized. No normalized here, actual formula below. Support arbitrary
variable {g:Shelf F α V}
lemma compose (h:Arms N (fun i j=> a i j (x i j)) k q (fun i=>(d i)⁻¹) g) (hh:∀ᶠ i in atTop, 0 < d i)(hf: Arms N x k p (fun _=>1) a) (hy : N.Rush s fun i=>(d i)⁻¹)(he:p+s ≤ 0): Budget N x k q (fun i j=>g i j ∘ a i j) := by
   obtain ⟨f,h',H⟩:=h.cap; obtain ⟨l,hl,hL⟩:= hf.cap; let u i:= l i*(d i)⁻¹; have hu:N.Rush 0 u:= (hl.times hy rfl).mono he; let Q i:= k.factorial*f i*(1+(1+u i))^k;
   have ht:N.Rush 0 (fun i=>(1+(1+u i))^k):= by simpa only [zero_mul (k:ℝ)] using! ((Rush.settle 1).blend ((Rush.settle 1).blend hu)|>.powers k);
   refine ⟨Q,(h'.multiplier (k.factorial:ℝ)).times ht (add_zero q), ?_⟩; filter_upwards [H,hL,hh] with i hi hr hp; have hv: 0≤u i:= mul_nonneg hr.1 (inv_pos.mpr hp).le; refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hi.1) (by positivity),fun j=>?_⟩;
   exact (Brush.trail (hi.2 j) ((hr.2 j).climb (v:=u i*d i) (le_of_eq (by unfold u; field_simp)) le_rfl) (h:=hp) (mul_inv_cancel₀ hp.ne' |>.le)).trim
lemma graft (hX : Arms N (fun i j=> a i j (x i j)) k q 1 g) (he : Budget N x k p a)(hf:p≤0): Budget N x k q (fun i j=>g i j ∘ a i j):= by
   have ht: (fun i:ℕ=>(1:ℝ)⁻¹) = (1:ℕ→ℝ):= funext fun _=> inv_one; exact compose (d:=1) (ht.symm ▸ hX) (Eventually.of_forall fun _=> zero_lt_one) he (Rush.settle 1⁻¹) (by rwa [add_zero])
end Budget
end
end YM.Contacts.Loom
