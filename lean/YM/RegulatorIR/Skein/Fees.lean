import YM.RegulatorIR.Skein.Tide

/-!
# Γ-curves with anchor. Publications not counted over volume.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Train Pupil
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {I X Y W:Type}{t n p s e:ℕ}
-- one tensor product frame with one held leg (index i of one slot), both row and column costs at that quota
lemma family_hold {Ω:Fin t→ Type}(f:∀ j,Ω j→ℝ≥0∞) (i:Fin t)(V: Ω i → Prop) : (∑' p:{p:∀ j,Ω j // V (p i)}, ∏ k,f k (p.val k))= (∑'v:{v:Ω i // V v},f i v.val)*∏ j∈(univ.erase i), (∑'v,f j v) :=by
 let g(j: Fin t)(w: Ω j):= if h:j=i then if V (h ▸ w) then f j w else 0 else f j w
 have hz : (∑' p:{p:∀ j,Ω j // V (p i)}, ∏ k,f k (p.val k)) = ∑' p: ∀ j,Ω j, (if V (p i) then ∏ j,f j (p j) else 0):=by convert tsum_subtype {p:∀ j, Ω j| V (p i)} (fun p=> ∏ j,f j (p j)) using 1 <;> rfl
 have hv(x:Ω i) : g i x= if V x then f i x else 0:= dif_pos rfl -- reduction
 have hp(j:Fin t)(x:Ω j)(h:j≠i) : g j x=f j x:= dif_neg h
 have h(x:∀ j,Ω j):(if V (x i) then ∏ j,f j (x j) else 0)=∏ j,g j (x j):=by
    split
    next he=> rw [← mul_prod_erase _ _ (mem_univ i),← mul_prod_erase Finset.univ (fun j=>g j (x j)) (mem_univ i),hv,if_pos he];exact congr_arg (f i (x i)*·) (prod_congr rfl (fun j hj=> (hp j (x j) (mem_erase.mp hj).1).symm))
    next he => exact (prod_eq_zero (mem_univ i) (show g i (x i)=0 from (hv _).trans (if_neg he))).symm
 rw [hz];simp_rw [h];rw [Train.tsum_family]; nth_rw 1 [← mul_prod_erase _ _ (mem_univ i)]
 have he: (∑' v,g i v)= (∑'v:{v:Ω i//V v},f i v.val):=by simp_rw [hv]; convert (tsum_subtype {v:Ω i| V v} (f i)).symm using 1 <;> rfl
 rw [show (∑' v,g i v)= _ from he]; exact congr_arg (fun x=>_*x) (prod_congr rfl (fun j hj=> tsum_congr fun v=> hp j v (mem_erase.mp hj).1))

variable {Γ:Curve X Y}{ℓ:Tariff W}{a:X→W}{b:Y→W}

def plotK (K:X→ Packet Y s)(ℓ:Tariff W) (a:X→ W)(b:Y→W)(i:Fin s)(t:Y)(x:X): ℝ≥0∞:= let U:= (Premium.rooted ℓ (a x)).uses b; quota (fun v:Hold i t=>K x v.val) (fun v=> U.width v.val)
structure Curves (Γ:Curve X Y)(ℓ:Tariff W)(a:X→ W)(b:Y→W)(i:ℕ) (C:ℝ≥0∞) : Prop where
 earlier (x:X) : markQ ((Premium.rooted ℓ (a x)).uses b) (Γ x i) ≤ C
 after (j:Fin (i+1))(t:Y): (∑' x,plotK (fun x=>Γ x i) ℓ a b j t x)≤ C
lemma escorts (Γ:Curve X Y)(ℓ:Tariff W)(a:X→W)(b:Y→W)(H:∀ i≤ s, ∃ c:ℝ≥0∞, c≠⊤∧ Curves Γ ℓ a b i c) : Acres Γ s:=by
 intro i hi y; obtain ⟨c,hc,K⟩:= H i hi; apply ne_top_of_le_ne_top hc; apply le_trans _ (K.after 0 (y 0)); rw [quota_base]; apply ENNReal.tsum_le_tsum; intro p; let u : Hold (0:Fin (i+1)) (y 0) := ⟨y,rfl⟩
 unfold plotK; exact ((mul_one _).ge.trans (mul_le_mul_right (Premium.width_unit ..) _)).trans (term_le _ _ u)
section
variable (Γ:Curve X Y)(ℓ:Tariff W)(a:X→W)(b:Y→W)(T:Packet X t) (g:Fin t→ℕ)
lemma series_bill (x:Tuple X t)(C:Fin t →ℝ≥0∞)(H:∀ i,Curves Γ ℓ a b (g i) (C i))(i:Fin t)(j:Fin (g i+1))(y:Y): Stalk.scopeQ (fun v:Tuple Y (t+charge g)=> v (Train.stations g ⟨i,j⟩)) (tracked Γ g x) (ℓ.uses b).diameter y ≤ ((ℓ.uses a).diameter x *plotK (fun x=>Γ x (g i)) ℓ a b j y (x i))*∏ k∈ univ.erase i,C k :=by
 let f:= Train.stations g ⟨i,j⟩;let F:= Hold (X:=Y) f y
 let x₀(k:Fin t):= (Premium.rooted ℓ (a (x k))).uses b
 let E:=Train.setting g Y
 let m:Hold f y ≃ {p:Train.Car g Y// p i j=y}:= Equiv.subtypeEquiv E (fun c=> (show c f=y ↔ (E c) i j=y from Iff.rfl))
 let v(k:Fin t)(p:Tuple Y (g k+1)):= ‖Γ (x k) (g k) p‖ₑ* (x₀ k).width p
 let u:= (ℓ.uses a).diameter x
 have hp(z:Tuple Y (t+charge g)): (ℓ.uses b).diameter z≤ u*∏ k:Fin t,(x₀ k).width (E z k):=by have hh:=across_bill g (Premium.free ℓ) a b x z; change Premium.width (Premium.free (ℓ.uses b)) z≤ Premium.width (Premium.free (ℓ.uses a)) x *_ at hh; simpa only [Premium.free_cost] using hh
 unfold Stalk.scopeQ quota; let Z:= {p:∀ k:Fin t,Tuple Y (g k+1)// p i j=y}
 change (∑' v:F,‖tracked Γ g x v.val‖ₑ* (ℓ.uses b).diameter v.val)≤ _;rw [← m.symm.tsum_eq]
 calc
    _ ≤ u* (∑' p: Z, ∏ k,v k (p.val k)):=by
       rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro w; let M:Tuple Y (t+charge g):=(m.symm w).val; have hh:E M=w.val:=congr_arg (·.val) (m.apply_symm_apply w); apply le_trans (mul_le_mul_right (hp M) _); apply le_of_eq
       change ‖trips Γ g x (E M)‖ₑ*(u*∏ k,(x₀ k).width (E M k))=_; rw [hh,Train.units,mul_left_comm]; unfold v; rw [Finset.prod_mul_distrib]
    _ ≤ _:=by
       rw [show (∑' p:Z, ∏ k, v k (p.val k)) = _ from family_hold v i (fun p=>p j=y)]; rw [← mul_assoc]; apply mul_le_mul_right; exact prod_le_prod' (fun z _ => ((H z).earlier (x z)))
lemma advice (C:Fin t →ℝ≥0∞)(H:∀ i,Curves Γ ℓ a b (g i) (C i)){v:ℝ≥0∞}(h: localQ (ℓ.uses a) T v): localQ (ℓ.uses b) (series Γ g T) (v * ∏ i,C i):=by
 intro i y; obtain ⟨⟨j,k⟩,rfl⟩:= (Train.stations g).surjective i; let f:=Train.stations g ⟨j,k⟩;let V:= Hold f y;let w:= ℓ.uses a;let U:= ℓ.uses b;let D(x:X):= plotK (fun x=>Γ x (g j)) ℓ a b k y x;let c:=∏ k∈ univ.erase j,C k
 let g'(x:Tuple X t)(p: V):= T x * tracked Γ g x p.val
 have hp(x:Tuple X t): quota (g' x) (fun p=>U.diameter p.val) ≤ (D (x j)*(‖T x‖ₑ * w.diameter x))*c:=by
    rw [quota_times]; exact (mul_le_mul_right (series_bill Γ ℓ a b g x C H j k y) ‖T x‖ₑ).trans_eq (by unfold c D; ac_rfl)
 apply le_trans (inside_quota (fun v x=> g' x v) (fun z=>U.diameter z.val)) ?_
 unfold quota;rw [ENNReal.tsum_comm]
 apply le_trans (ENNReal.tsum_le_tsum hp);rw [ENNReal.tsum_mul_right];nth_rw 1 [← mul_prod_erase _ C (mem_univ j)]; rw [← mul_assoc]; apply mul_le_mul_left
 rw [← ENNReal.tsum_fiberwise _ (g:=fun x:Tuple X t=> x j)]; apply le_trans _ (mul_le_mul_right ((H j).after k y) v)
 rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro i
 have hh:∀ x:Hold j i,x.val j=i:=fun x=> x.property;change (∑' x:Hold j i,D (x.val j) * _ )≤ v*D i; simp_rw [hh,ENNReal.tsum_mul_left]; rw [mul_comm v];exact mul_le_mul_right (h j i) _
end
end YM.RegulatorIR.Skein
