import YM.AllOrder.Floe.License
import YM.AllOrder.Ink.Sponsor
import YM.AllOrder.Ink.Origin
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M J U₀ E₀:ℕ} {a C D b:ℝ}
namespace Money
open Method
variable {V:Type} {Λ:V→ℝ}{f g:V→Bills α}{Ad:Side→Prop}
variable {A:V→Stalk α α}{P:V→ℝ}(hP:CreditF Λ 0 P)(ht:0<a)(H:∀ v,Belt (A v) a (P v))
lemma Weight.star_cube {P Q T: V→Side→ℝ}(P':Weight Λ U₀ P)(Q':Weight Λ E₀ Q)(T':Weight Λ J T)(α:Type)[Fintype α](k l : ℕ): Weight Λ (U₀+E₀+J+8) (fun i n=> cubeD α n k l (P i n) (Q i n) (T i n)):= by simpa only [Nat.add_comm, Nat.add_assoc,Nat.add_left_comm, Nat.add_zero, Nat.reduceAdd,cubeD] using (Weight.grid α Λ).times ((Weight.grid α Λ).times (P'.times ((Q'.times (Weight.fixed Λ _ (honor_pos k).le)).times (T'.times (Weight.fixed Λ _ (honor_pos l).le)))))
include H hP ht
lemma License.join (h:License Ad Λ f a k J)(h':License Ad Λ g a N U₀)(hb:0<b)(hr:b*(N+1:ℕ)≤a): License Ad Λ (fun i n=> spark (A i) (f i n) (g i n)) b ((k-1)+(N-1)) (U₀+J+12) := by
 obtain ⟨F,C,D,hC,hD,h⟩:=h; obtain ⟨G,P',U,hg,hU,h'⟩:=h'
 
 have hy i:= spark_num _ (H i) (hP.nonneg _) ht (h i) (h' i) hb.le hr (hD.nonneg i) (hU.nonneg i)
 let k':ℝ:=k; let b':ℝ:=N
 refine ⟨(fun i=>embrace (A i) (F i) (G i)), _, _, ((freeC k' (Nat.cast_nonneg _)).mul ((freeC b' (Nat.cast_nonneg _)).mul (hP.mul hg))).mul hC|>.up (by omega), ?_, hy ⟩
 let P₀ := Weight.lift hP
 refine Weight.stamp ?_ ?_
 · apply (Weight.star_cube P₀ hD (((Weight.low Λ).times (Weight.lift hg)).stamp (hU.ups (Nat.le_add_left ..))) α k N).ups; omega
 apply (Weight.star_cube P₀ ((Weight.low Λ).times (Weight.lift hC)) hU α k N).ups; omega

omit H hP
-- cost after linear port along post stalk
variable {L:V→Stalk α β}(hf: ∀ v,Belt (L v) a (P v))
include hP hf
lemma License.move (h:License Ad Λ f a k J): License Ad Λ (fun i n=> f i n ∘ know (L i) n) a k (J+4*k) := by
 let t:=a; have hσ:0<t:= ht; let he:=hf; obtain ⟨F,C,D,hC,hD,h⟩:=h; let g(i n):= know (L i) n
 have hc i:=hP.nonneg i; let K(i:V)(n:Side):=1+(Fintype.card (Leaf n β):ℝ)* P i; let g0:=((freeC (Λ:=Λ) 1 zero_le_one).add ((freeC (Fintype.card β:ℝ) (by positivity)).mul hP)).raise k; let P':=fun i n=> D i n*K i n^k
 have hK:Weight Λ 4 K:= ((Weight.fixed _ _ zero_le_one).ups (Nat.zero_le 4)).stamp ((Weight.grid β Λ).times (Weight.lift hP)); have hZ i:= Method.well _ (he i) hσ.le (hc i) (F i) (h i).1
 refine ⟨(fun i=> Method.confirm (L i) (F i)),_,P', (g0.mul hC).up (by simp),hD.times (hK.raise _),fun i=>⟨hZ i,fun n hn=>?_⟩⟩; let A:= f i n-(F i).table n; let r:= dearth t n; have hv := (h i).2 n hn
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
omit hf
include H
lemma License.furnish (h:License Ad Λ f a k J): License Ad Λ (fun v n=> flicker (A v) n (f v n)) a (k-2) (J+8) := by
 let x:= a; have hh:= ht; let hX:=H; obtain ⟨F,C,D,hC,hD,h⟩:=h
 let w:= ((k*k:ℕ):ℝ); have hw : 0 ≤ w:= Nat.cast_nonneg _; let d(v:V)(n:Side):ℝ:=Fintype.card (Leaf n α); let u:=freeC (Λ:=Λ) w hw; let hu:= u.mul (hP.mul hC)
 let Z v:= plan (F v) (funds (A v)); have hg v:= crux (A v) (F v) (h v).1 (hX v) hh.le (hP.nonneg v);
 let T₀(v:V)(n: Side):ℝ := Fintype.card (Site n) * (w*(P v*C v)); let D' := fun (v:V) (n: Side)=> d v n*(d v n*(P v*((D v n *honor k) * honor (k-1))))
 have hT: Weight Λ (4+(0+(0+J))) T₀:= (Weight.low Λ).times (Weight.lift hu); have h' : Weight Λ (4+(4+(0+(J+0+0)))) D':= Weight.times (Weight.grid α Λ) ((Weight.grid α Λ).times ((Weight.lift hP).times ((hD.times (Weight.fixed Λ _ (honor_pos k).le)).times (Weight.fixed Λ _ (honor_pos _).le))))
 refine ⟨Z,_,_,hu.up (by omega), Weight.stamp (hT.ups (by omega)) (h'.ups (by omega)),fun v=> ⟨hg v,fun n hn=>?_⟩⟩; let f':=f v n; let g':=(F v).table n; let X':=flicker (A v) n; let R:= dearth x n; have hx : Prices k (D v n* R) (f'-g'):= (h v).2 n hn; have hE:= prices_flick (A v) (hX v) (hP.nonneg _) hh.le hx; let Y:=(Z v).table n
 have hC: Prices (k-2) (T₀ v n * R) (X' g'-Y):= by
    unfold T₀; rw [mul_assoc (Fintype.card (Site n):ℝ), show w*(P v*C v)*R=w*((R*P v)*C v) from (by ring)]; exact carbon (H:= (h v).1) (hX v) hh.le (hP.nonneg _) _ -- arguments
 have hu: Prices (k-2) (D' v n * R) (X' (f'-g')):= by rw [show D' v n * R=d v n *(d v n*(P v*((D v n*R*honor k)*honor (k-1)))) from (by unfold D'; ring)]; exact hE
 change Prices (k-2) ((T₀ v n+D' v n)*R) (X' f'-Y); rw [add_mul, show X' f'-Y = (X' g'-Y)+ X' (f'-g') from ?_]; · exact price_add hC hu
 have hv := ((h v).1.binding (n:=n) hh.le).2.1.read; rw (occs:=.pos [1]) [← add_sub_cancel g' f', show X' (g'+ (f'-g'))=_ from (flicker_plus (A v) _ _ hv hx.2.1.read)]; abel
end Money
end YM.AllOrder.Ink

