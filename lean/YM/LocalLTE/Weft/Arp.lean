import YM.LocalLTE.Weft.Hex
/-! Weft scaled charges in powers at FIXED knobs. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Set Metric Function MeasureTheory Finset
open Tensor Analysis ConnectedActivityE6.Blaze
open scoped Topology BigOperators Classical ContDiff
variable {E F A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup A][NormedSpace ℝ A]
variable {k n m : ℕ} {C d v w :ℝ}
def orb (s:ℝ): E→L[ℝ] E:= s • ContinuousLinearMap.id ℝ E
lemma orbJ {f:E→F}(s:ℝ)(h:ContDiffAt ℝ (↑k) f 0): iteratedFDeriv ℝ k (fun x:E=> f (s • x)) 0= s^k • iteratedFDeriv ℝ k f 0:=by
   change iteratedFDeriv ℝ k (f ∘ orb s) _=_
   rw [linear_pull (orb s) (by rw [map_zero]; exact h), map_zero]; ext x
   change iteratedFDeriv ℝ k f 0 (fun i=> s • x i)=_; rw [(iteratedFDeriv ℝ k f 0).map_smul_univ]; simp
lemma orbT {f:E→F}(s:ℝ)(h:ContDiffAt ℝ (↑k) f 0): coeff (fun x:E=> f (s • x)) k 0= s^k • coeff f k 0:=by unfold coeff; rw [orbJ s h]; exact smul_comm ..
lemma orb_cost {f:E→F}(s:ℝ)(h:Brush k C 1 f 0)(hs:s∈clip): Brush k C 1 (fun x=> f (s • x)) 0:=by
    have h₁: ‖orb (E:=E) s‖≤1:=by unfold orb; rw [norm_smul,Real.norm_of_nonneg hs.1.le]; exact mul_le_one₀ hs.2 (norm_nonneg _) ContinuousLinearMap.norm_id_le
    have h₂:= Brush.reading (orb s) (show Brush k C 1 f ((orb s) 0) from (by rw [map_zero]; exact h)) h₁
    rw [one_mul] at h₂; exact h₂
/-- A jet order valuation. We only require lower powers inside the actual finite jet
   budget. -/
def Null (k j:ℕ)(f:E→F):Prop:= ∀ i,i≤j → i<k → iteratedFDeriv ℝ i f 0=0
/-- Combined radius bandwidth and scaling for germs.
   `Laurent` field-side weights recorded by z↦f z; value is O(1) when input directions are
   magnified in the metric of small curvature g, marked separately. -/
structure Arp (k j:ℕ)(C:ℝ)(f:ℝ→E→F):Prop where
    hex : Hex k f
    brush (s:ℝ):s∈clip → Brush j C 1 (fun x=> f s (s • x)) 0
variable {f g:ℝ→E→F}
namespace Arp
variable (hf:Arp k n C f) {K:ℕ} {D:ℝ}
include hf
lemma climb (h:k ≤ K)(he:C≤ D) : Arp K n D f := ⟨hf.hex.grow h,fun i hi=> (hf.brush i hi).climb he le_rfl⟩
-- use calendar irrelevant equality e.g. g values outside clip
lemma adjust (hp:Set.EqOn f g clip): Arp k n C g:= ⟨hf.hex.change hp,fun i hi=> (hf.brush i hi).shimmy (by simp_rw [hp hi]; exact EventuallyEq.refl ..)⟩
omit hf
lemma zero' : Arp k n 0 (fun (_:ℝ) (_:E)=> (0:F)) := ⟨Hex.constant _,fun _s _=> (norm_zero (E:=F)) ▸ Brush.certified zero_le_one _⟩ -- edit
lemma still {u:E→F}(h:Brush n C 1 u 0): Arp 0 n C fun _=>u:= ⟨Hex.constant u,fun s hs=> orb_cost s h hs⟩
include hf
lemma nonneg : 0≤C := (hf.brush 1 ⟨zero_lt_one,le_rfl⟩).nonneg
lemma sumAdd {u:ℝ→E→F}(hg:Arp m n w u) : Arp (max k m) n (C+w) (fun s=> f s+u s):= ⟨(hf.hex.grow (le_max_left k m)).add (hg.hex.grow (le_max_right k m)),fun i hi=> (hf.brush i hi).gathering (hg.brush i hi)⟩
lemma scales (s:ℝ): Arp k n ( |s| *C) (fun i=> s • f i):= ⟨hf.hex.oneZ _,fun i hi=> (hf.brush i hi).smul s⟩
omit hf
lemma sumQ {ι:Type*}(A:Finset ι)(v:ι→ℝ→E→F)(C:ι→ℝ)(h:∀ i∈A, Arp k n (C i) (v i)): Arp k n (∑ i∈A,C i) (fun x=>∑ i∈A, v i x) :=by
   refine ⟨Hex.total A fun i hi=>(h i hi).hex, fun i hi=>?_⟩; simp_rw [Finset.sum_apply]; exact Brush.spree _ _ _ zero_le_one fun j hj=> (h j hj).brush i hi
lemma mult {f:ℝ→E→ℝ} (hf:Arp k n C f) {g :ℝ→E→ℝ}(hg:Arp m n v g) : Arp (k+m) n ((C*v)*(1+(1+1))^n) (fun s=> f s * g s):= ⟨Hex.invert (fun i=> (hf.hex.use i).mul (hg.hex.use i)),fun i hi=> ((hf.brush i hi).paints (hg.brush i hi)).trim⟩
lemma reduced {u:E→F} {h:Brush k C 1 u 0}(h₁:Null n k u): Arp n k C (fun s=> (s^n)⁻¹ • u):=by
   refine ⟨?_,fun i hi=>?_⟩
   · exact Hex.change (Hex.held (k:=n) ⟨0,by omega⟩ u) fun i _=>by unfold mark; simp
   have hp: ContDiffAt ℝ (↑k) (u ∘ orb i) 0:= h.smooth.comp_of_eq 0 ((orb i).contDiff.contDiffAt)  (fun _ _=> trivial) (map_zero _)
   refine Brush.offer.mpr ⟨hp.const_smul ((i^n)⁻¹),fun j hj=>?_⟩
   unfold normJ; change ‖iteratedFDeriv ℝ j ((i^n)⁻¹ • (u ∘ orb i)) 0‖ ≤ C; rw [iteratedFDeriv_const_smul_apply (hp.of_le (by exact_mod_cast hj)), show iteratedFDeriv ℝ j (u ∘ orb i) 0=i^j • iteratedFDeriv ℝ j u 0 from orbJ i (h.smaller hj).smooth]
   by_cases ht:j<n
   · rw [h₁ j hj ht,smul_zero,smul_zero,norm_zero]; exact h.nonneg
   have he:0 < i:= hi.1
   rw [smul_smul,norm_smul,Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg he.le _)) (pow_nonneg he.le _))]; apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (Brush.offer.mp h|>.inside _ hj); rw [inv_mul_eq_div,div_le_one (pow_pos he _)]; exact pow_le_pow_of_le_one he.le hi.2 (by omega)
include hf
lemma polyP (t:ℕ): Arp (t+k) n C (fun i=> i^t • f i):= by
   let I: J t:=⟨2*t,by omega⟩
   have h: Hex t (fun i:ℝ=> i^t):= Hex.change (Hex.held I (1:ℝ)) fun i hi=>by
       have he:0 < i:=hi.1
       change i^(2*t)/i^t*1=_; rw [mul_one,two_mul,pow_add,mul_div_cancel_right₀ _ (pow_ne_zero _ he.ne')]
   refine ⟨h.wallet hf.hex,fun i hi=> ((hf.brush i hi).smul (i^t)).climb (mul_le_of_le_one_left hf.nonneg ?_) le_rfl⟩ -- binder
   rw [norm_pow,Real.norm_of_nonneg hi.1.le]; exact pow_le_one₀ hi.1.le hi.2
omit hf
lemma twisted {z:F→L[ℝ] E} {f:ℝ→E→A} (hf:Arp k n C f) (h:‖z‖≤1) : Arp k n C (fun i x=> f i (z x)):=by
   refine ⟨Hex.invert (fun i=> hf.hex.use _),fun s hs=>?_⟩
   have hx := Brush.reading z (show Brush n C 1 (fun x=> f s (s • x)) (z 0) from (by rw [map_zero]; exact hf.brush s hs)) h
   simp_rw [map_smul]; rw [one_mul] at hx; exact hx
include hf
lemma smooth {s:ℝ}(hs:s∈clip): ContDiffAt ℝ (↑n) (f s) 0:=by
   have hq := hf.brush s hs
   let V:= orb (E:=E) s⁻¹
   have hx: ContDiffAt ℝ (↑n) (fun i=> f s (s • V i)) 0 := hq.smooth.comp_of_eq 0 (V.contDiff.contDiffAt)  (fun _ _=> trivial) (map_zero V) -- order
   rwa [show (fun i=> f s (s • V i))=f s from funext fun i=>by rw [show s • V i=i from smul_inv_smul₀ hs.1.ne' i]] at hx
lemma postage (i:ℕ)(hp:i≤ n): ∀ s∈clip, ‖s^i • coeff (f s) i (0:E)‖≤ C:=by
   intro s hs; rw [← orbT s (hf.smooth hs|>.of_le (by exact_mod_cast hp))]; unfold coeff; rw [norm_smul]
   exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv, Real.norm_of_nonneg (by positivity : 0 ≤ (i.factorial:ℝ))]; exact (inv_le_one₀ (by positivity : 0 < (i.factorial:ℝ))).mpr (by exact_mod_cast Nat.factorial_pos _))).trans ((Brush.offer.mp (hf.brush s hs)).inside i hp)
lemma coeffHex (i:ℕ)(hp:i≤ n): Hex k (fun s=> coeff (f s) i 0) := hf.hex.smoothWork (fun _ hs=> (hf.smooth hs).of_le (by exact_mod_cast hp))
lemma pays (i:ℕ)(hp:i≤n)(j:J k): let f':=pick k (fun s=> coeff (f s) i 0) j; ‖f'‖≤(∑ l:J k,|slate k l j|/probe k l^i)*C ∧ (j.val+i<k→ f'=0):=by
    intro f'; exact ⟨caisson _ (hf.postage i hp),vanish (hf.coeffHex i hp) (hf.postage i hp) j⟩
end Arp
end YM.LocalLTE.Weft
