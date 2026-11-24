import YM.AllOrder.Ink.Sponsor
import YM.AllOrder.Ink.Origin
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
open Method
variable {V:Type} {Λ:V→ℝ}{f g:V→Bills α}{Ad:Side→Prop}
variable {A:V→Stalk α α}{P:V→ℝ}(hP:Grade Λ P)(ht:0<a)(H:∀ v,Belt (A v) a (P v))
lemma Pay.star_cube {P Q T: V→Side→ℝ}(P':Pay Λ P)(Q':Pay Λ Q)(T':Pay Λ T)(α:Type)[Fintype α](k l : ℕ): Pay Λ (fun i n=> cubeD α n k l (P i n) (Q i n) (T i n)):= (Pay.grid α Λ).times ((Pay.grid α Λ).times (P'.times ((Q'.times (Pay.fixed Λ _ (honor_pos _).le)).times (T'.times (Pay.fixed Λ _ (honor_pos _).le)))))
include H hP ht
lemma Apt.join (h:Apt Ad Λ f k)(h':Apt Ad Λ g N): Apt Ad Λ (fun i n=> spark (A i) (f i n) (g i n)) ((k-1)+(N-1)) := by
 rcases h with ⟨t,h0,h⟩; rcases h' with ⟨c,hc,h'⟩; let b:= min a (min c t); have hb:0<b:=by unfold b; exact lt_min ht (lt_min hc h0)
 have hu i := Belt.debt (H i) (min_le_left a (min c t)) le_rfl
 let σ:= b/(N+1:ℕ); have hs:0<σ:=div_pos hb (by positivity); have ht:σ*(N+1:ℕ)≤b := le_of_eq (div_mul_cancel₀ _ (by positivity))
 rcases squeeze h (show b≤t from (min_le_right ..).trans (min_le_right ..)) (le_refl k) with ⟨F,C,D,hC,hD,h⟩
 obtain ⟨G,P',U,hg,hU,h'⟩:= squeeze h' (show b ≤ c from (min_le_right ..).trans (min_le_left ..)) (le_refl N)
 have hy i:= spark_num _ (hu i) (hP.nonneg _) hb (h i) (h' i) hs.le ht (hD.nonneg i) (hU.nonneg i)
 let k':ℝ:=k; let b':ℝ:=N
 refine ⟨σ,hs,(fun i=>embrace (A i) (F i) (G i)), _, _, ((gia k' (Nat.cast_nonneg _)).mul ((gia b' (Nat.cast_nonneg _)).mul (hP.mul hg))).mul hC, ?_, hy ⟩
 let P₀ := Pay.lift hP; exact (Pay.star_cube P₀ hD (((Pay.low Λ).times (Pay.lift hg)).stamp hU) α k N).stamp (Pay.star_cube P₀ ((Pay.low Λ).times (Pay.lift hC)) hU α k N)

omit H hP
-- cost after linear port along post stalk
variable {L:V→Stalk α β}(hf: ∀ v,Belt (L v) a (P v))
include hP hf
lemma Apt.move (h:Apt Ad Λ f k): Apt Ad Λ (fun i n=> f i n ∘ know (L i) n) k := by
 obtain ⟨b,h0,h'⟩:=h; let t:= min b a; have hσ:0<t:= lt_min h0 ht; have he i:= Belt.debt (hf i) (min_le_right b a) le_rfl
 obtain ⟨F,C,D,hC,hD,h⟩:= Apt.squeeze h' (min_le_left b a) (le_refl k); let g(i n):= know (L i) n
 have hc i:=hP.nonneg i; let K(i:V)(n:Side):=1+(Fintype.card (Leaf n β):ℝ)* P i; let g0:=((gia (Λ:=Λ) 1 zero_le_one).add ((gia (Fintype.card β:ℝ) (by positivity)).mul hP)).raise k; let P':=fun i n=> D i n*K i n^k
 have hK:Pay Λ K:= (Pay.fixed _ _ zero_le_one).stamp ((Pay.grid β Λ).times (Pay.lift hP)); have hZ i:= Method.well _ (he i) hσ.le (hc i) (F i) (h i).1
 refine ⟨t,hσ,(fun i=> Method.confirm (L i) (F i)),_,P', g0.mul hC,hD.times (hK.raise _),fun i=>⟨hZ i,fun n hn=>?_⟩⟩; let A:= f i n-(F i).table n; let r:= dearth t n; have hv := (h i).2 n hn
 rw [Method.run_total _ (he i) hσ.le (hc i) _ (h i).1];
 refine ⟨mul_nonneg ((hD.times (hK.raise k)).nonneg i n) (Real.exp_pos _).le,hv.2.1.lead (g i n),fun x=>?_⟩
 change |A (g i n x)|≤ _; have hx: roi (g i n x) ≤ K i n * roi x:= by
     let w : ℝ:= Fintype.card (Leaf n β); have he0: 0≤w:= by unfold w; positivity
     have hC₀(y:Leaf n α): ‖g i n x y‖ ≤ w*(P i*‖x‖):= by
         change ‖∑ j:Leaf n β,direct _ n y j*x j‖ ≤ _; refine ((norm_sum_le ..).trans (Finset.sum_le_sum (s:= Finset.univ) (g:=fun _=> P i* ‖x‖) ?_)).trans ?_; · intro j _; rw [norm_mul]; exact mul_le_mul ((hf i).norm_direct ht.le _ _) (norm_le_pi_norm ..) (norm_nonneg _) (hc _)
         simp [w]
     unfold roi; change _ ≤ (1+w* P i)*(1+‖x‖); have ht:= (pi_norm_le_iff_of_nonneg (show 0≤ w*(P i*‖x‖) from (by have hh:=hc i; positivity))).2 hC₀; nlinarith [norm_nonneg x,hc i]
 refine (hv.2.2 _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx k) hv.1).trans_eq ?_);
 rw [mul_pow]; change D i n*r*(K i n^k* _) = D i n*K i n^k* r *(roi x)^k; ring
end Money
end YM.AllOrder.Ink
