import YM.XSpace.ProbeLine
/-! # All derivative spectators regular through OFF-NULL legs of Maxwell kernel -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.ProbeLine
open Set Filter Function MeasureTheory Maxwell Analysis Tensor
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial

-- rationals generated on away
inductive Soup : (E4→ℝ)→Prop
| delta (c:ℝ): Soup (fun _=>c)
| axis (a:Axis): Soup (fun x=>x a)
| squared: Soup (fun x=> (rsq x)⁻¹)
| add {x y}: Soup x→Soup y→ Soup (x+y)
| mul {x y}: Soup x→Soup y→ Soup (x*y)
| joins {f g}:Soup f→EqOn f g away→Soup g

namespace Soup
lemma scales (r:ℝ) {f:E4→ℝ} (h:Soup f):Soup (r • f):= (Soup.delta r).mul h
lemma neg {f:E4→ℝ} (h:Soup f):Soup (-f):=by simpa using scales (-1) h
lemma sub {f g:E4→ℝ} (h:Soup f) (hg:Soup g):Soup (f-g):=by simpa only [sub_eq_add_neg] using h.add hg.neg
lemma sum {ι : Type*}(f:ι→E4→ℝ) (S : Finset ι)(h:∀ i∈S,Soup (f i)): Soup (fun x=>∑ i∈S,f i x):= by induction S using Finset.induction_on with | empty=> simp; exact delta 0 | @insert x y hp ih=>simp_rw [Finset.sum_insert hp]; exact (h x (Finset.mem_insert_self ..)).add (ih fun x hx=> h x (Finset.mem_insert_of_mem hx))

lemma feel {f:E4→ℝ}(h:Soup f) {x:E4} (hx:x∈away): ContDiffAt ℝ ∞ f x:= by
  have hu:= norm_pos_iff.mpr (show x≠0 from hx)
  induction h with
  | delta c=> exact contDiffAt_const
  | axis a=> fun_prop
  | squared=> exact (contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp; positivity)
  | add _ _ hp hq=> exact hp.add hq
  | mul _ _ hp hq=> exact hp.mul hq
  | joins _ hg ih=> exact ih.congr_of_eventuallyEq ((show ∀ᶠ w in 𝓝 _, w∈away from open_away.mem_nhds hx).mono (fun _ hx=> (hg hx).symm))

lemma rise {f:E4→ℝ} (h:Soup f) (v:E4): Soup (D v f):= by
  let y x:= (rsq x)⁻¹
  induction h with
  | delta c => rw [show D v (fun _:E4=>c)=fun _=>0 from funext fun i=>by simp [D]]; exact delta _
  | axis i => apply joins (delta (v i)); intro p hp
              change _= fderiv ℝ (compAxis i) p v; rw [(compAxis i).fderiv]; rfl
  | squared=>
    let V (x:E4):= inner ℝ x v
    have hv : Soup V:= by simp_rw [show V=(fun x:E4=>∑ i:Axis,x i*v i) from funext fun x=> Free.inner4 x v]; exact sum _ _ (fun i _=> (axis i).mul (delta (v i)))
    apply joins ((Soup.scales (-2) hv).mul (squared.mul squared)); intro p hp
    let A:= hasStrictFDerivAt_norm_sq p; have ht:‖p‖^2≠0:= by have hx:= norm_pos_iff.mpr (show p≠0 from hp); positivity
    have he:= ((hasFDerivAt_inv ht).comp p A.hasFDerivAt).fderiv
    change fderiv ℝ y p = _ at he
    change -2*V p*(y p*y p)= fderiv ℝ y p _; rw [he]; simp [two_smul,V,y,rsq]; ring
  | @add f g hf hg hp hq=>
    apply joins (hp.add hq); intro p h; dsimp [D]; rw [← show (fun x=> f x+g x)=(f+g) from rfl, fderiv_fun_add ((hf.feel h).differentiableAt (by simp)) ((hg.feel h).differentiableAt (by simp))];rfl
  | @mul f g hf hg hp hq=>
    apply joins ((hf.mul hq).add (hg.mul hp)); intro p h; dsimp [D]; rw [fderiv_mul ((hf.feel h).differentiableAt (by simp)) ((hg.feel h).differentiableAt (by simp))]; simp
  | joins hf hg hp=> exact hp.joins (fun x hx=> GermD v ((show ∀ᶠ w in 𝓝 _, w∈away from open_away.mem_nhds hx).mono fun _ hy=> hg hy))
lemma bare (i j a b):Soup (bareCurl i j a b):= by
  have he : Soup Green:= Soup.scales normal squared
  have hp (i k m) : Soup (curlOpp i k m):= by unfold curlOpp; apply sub <;> split_ifs <;> first|exact he.rise _|exact delta 0
  exact ((hp j a b).rise _).sub ((hp i a b).rise _)
lemma arise {f:E4→ℝ} (h:Soup f) (n:ℕ) (v:Fin n→E4):Soup (fun x=> Tensor.coeff f n x v):= by
  induction n generalizing f with
  | zero=> apply Soup.joins h; intro x _; exact (Tensor.coeff_apply_zero ..).symm
  | succ n ih=>
    apply Soup.joins (f:= (↑(n+1):ℝ)⁻¹ • (fun x=> Tensor.coeff (D (v 0) f) n x (Fin.tail v))) (Soup.scales _ (ih (h.rise (v 0)) _)); intro x hx
    change _= Tensor.coeff _ _ _ _; nth_rw 3 [← Fin.cons_self_tail v]; -- inspect
    rw [Tensor.coeff_apply_cons ((h.feel hx).of_le (WithTop.coe_le_coe.mpr le_top))]; rfl

lemma along {f:E4→ℝ}(h:Soup f) {m u x:E4}(hp:u≠0)(hx:cubic m u x≠0): ∃ c:ℂ, Proves (fun r:ℝ=> (↑(f (drifts m u x r)):ℂ)) c:= by
  induction h with
  | delta c=> exact ⟨_,Proves.unit _⟩
  | axis a=> exact ⟨_,corner_match ..⟩
  | squared=> simp_rw [Complex.ofReal_inv]; exact ⟨_,(square_match ..).inv hx⟩
  | add _ _ h g=> obtain ⟨c,H⟩:=h; obtain ⟨d,v⟩:=g; simp only [Pi.add_apply, Complex.ofReal_add]; exact ⟨_,H.add v⟩
  | mul _ _ h g=> obtain ⟨c,H⟩:=h; obtain ⟨d,v⟩:=g; simp only [Pi.mul_apply, Complex.ofReal_mul]; exact ⟨_,H.mul v⟩
  | joins hf he h=> obtain ⟨c,H⟩:=h; exact ⟨c,H.alter ((wandering _ _ _ hp).mono fun _ hx=>congr_arg Complex.ofReal (he hx))⟩
end Soup

variable {G:Gauge} {j k:ℕ}
lemma true_pole (p: Probe G j) (q: Probe G k): Soup (legKernel p q):= by
  have he (p q:Probe G j)(x y: Probe G k)(z:E4)(hz:z∈away):
      legKernel (p+q) x z=legKernel p x z+legKernel q x z ∧ legKernel p (x+y) z=legKernel p x z+legKernel p y z := by
    let T:= pairing (G:=G) (j:=j) (l:=k) (z:=z) hz
    constructor
    · exact LinearMap.congr_fun (T.map_add p q) x
    exact (T p).map_add ..
  have ht (v: Probe G j)(x y: Probe G k)(z:E4)(hz:z∈away)(t:ℝ): legKernel (t • v) x z=t*legKernel v x z ∧ legKernel v (t • y) z=t*legKernel v y z:=by
    let T:= pairing (G:=G) (j:=j) (l:=k) (z:=z) hz
    exact ⟨LinearMap.congr_fun (T.map_smul t v) _,(T v).map_smul ..⟩
  have zp (r: ℕ)(x: Probe G r)(i:ℕ):Soup (legKernel (0:Probe G i) x):= (Soup.delta 0).joins (fun v hv=> Eq.symm (LinearMap.congr_fun (map_zero (pairing (G:=G) (show v∈away from hv) (j:=i) (l:=r))) x))
  let T (j:ℕ):= {p : Probe G j| ∃ u c i m, p=constrain (G:=G) (fromF G u c i m)}
  have span (j :ℕ)(p:Probe G j) : p∈ Submodule.span ℝ (T j):= spans.symm ▸ Submodule.mem_top
  refine Submodule.span_induction (p:=fun v _=> Soup (legKernel v q)) ?_ (zp ..) (fun a b _ _ ha hb=> (ha.add hb).joins (fun x hx=> (he a b q q x hx).1.symm)) (fun t x h hx=> (Soup.scales t hx).joins (fun a ha=> (ht _ q q a ha t).1.symm)) (span j p)
  rintro v ⟨u,c,i,m,rfl⟩
  let a:=constrain (fromF G u c i m)
  have hz:Soup (legKernel a (0:Probe G k)):= (Soup.delta 0).joins (fun x hx=> Eq.symm ((pairing (show x∈away from hx) a).map_zero))
  refine Submodule.span_induction (p:=fun b _=> Soup (legKernel a b)) ?_ hz (fun p q _ _ hp hq=> (hp.add hq).joins (fun x hx=> (he a a p q x hx).2.symm)) (fun t y h H=> (Soup.scales t H).joins (fun p hp=> (ht a y y p hp t).2.symm)) (span k q)
  rintro _ ⟨v,d,w,n,rfl⟩
  let l x:= if c=d then (-1)^k * Tensor.coeff (fun z => Tensor.coeff (bareCurl i m w n) j z u) k x v else 0
  have hl : Soup l := by unfold l; split_ifs; exact Soup.scales _ (((Soup.bare ..).arise j u).arise k v); exact Soup.delta _
  apply hl.joins; intro x hx; have he:= raw_mixed u v i m w n c d hx
  exact he.symm
end YM.XSpace.ProbeLine
