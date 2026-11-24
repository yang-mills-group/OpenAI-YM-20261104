import YM.RegulatorIR.Gain.Lyre

/-!
# Weight lift through contiguous gauge replacement

Finite color vector. Substitutions through `$\Phi$` unweighted linear
canonical rows except explicit prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I J X Y Z:Type}{r m a:ℕ}

-- generate finite pet
section Color
abbrev Mood (G:Gauge):=(Fin 3 × G.ColorIndex)
-- pos addresses in Trip i

def pinTrip (t:Fin 3)(X:Trip G):G.Color:= (![X.1, X.2.1, X.2.2]:Fin 3→ G.Color) t

def lineTrip (G:Gauge): Trip G ≃ₗ[ℝ] (Mood G→ℝ) where
 toFun v i:= pinTrip i.1 v i.2
 invFun x:=(WithLp.toLp 2 (fun i=>x (0,i)),WithLp.toLp 2 (fun i=>x (1,i)),WithLp.toLp 2 (fun i=>x (2,i)))
 left_inv _ := rfl
 right_inv x:=by ext1 i; rcases i with ⟨i,r⟩;fin_cases i <;> rfl
 map_add' p q:=by ext1 i; rcases i with ⟨i,r⟩; fin_cases i <;> rfl
 map_smul' r p:=by ext1 i; rcases i with ⟨i,x⟩; fin_cases i <;> rfl

def key (G:Gauge)(i:Mood G) := (lineTrip G).symm (Pi.single i (1:ℝ))
lemma trip_splits (X:Trip G): X=∑ j:Mood G,lineTrip G X j • key G j:=by
 apply (lineTrip G).injective;rw [map_sum]; simp_rw [map_smul, key, LinearEquiv.apply_symm_apply]; ext1 u; rw [Finset.sum_apply]; simp [Pi.single_apply,mul_ite]

variable (G)
def fountain (j: G.ColorIndex)(t:ℕ) (p:Tuple (Mood G) (t+1)) :ℝ:= ((t+1).factorial:ℝ)⁻¹ * (iteratedFDeriv ℝ (t+1) (fun x:Trip G=> billU x j) 0 (key G ∘ p))
def pet (j:G.ColorIndex)(t:ℕ):Packet (Mood G) (t+1):= Packet.symmetry (fountain G j t)
lemma pet_eval (j:G.ColorIndex)(t:ℕ)(u:Trip G): strum (pet G j t) (lineTrip G u)=song G t j u:=by
 rw [pet,pluck,render_symmetry,← play]
 let D:=(iteratedFDeriv ℝ (t+1) (fun x:Trip G=>billU x j) 0).toMultilinearMap; let f:=(lineTrip G u : Mood G→ℝ); let p:= fountain G j t;let C:ℝ:= ((t+1).factorial:ℝ)⁻¹
 change (∑ x:Tuple (Mood G) (t+1),p x* (∏ i,f (x i)))= C*D (fun _=> u)
 rw [trip_splits u] -- check occurrences
 rw [D.map_sum (fun _ i=> f i • key G i),Finset.mul_sum]; apply sum_congr rfl; intro x _; rw [D.map_smul_univ (fun a=> f (x a)) (fun i=>key G (x i))]; unfold p fountain; change C*_ * _= C * ((∏ i, f (x i))* D (key G ∘ x)); change C*D (key G ∘ x)*_ =C*_;ring
lemma boots (j:G.ColorIndex) (u:Trip G): strum (pet G j 0) (lineTrip G u)=(u.1 j+u.2.1 j-u.2.2 j):=by rw [pet_eval,← song_jet, routeS,tale_base]; dsimp only; rw [crest_origin];simp [add_comm]
end Color

section Loom
variable [Fintype I]

def thread (K:Layer I X)(p:Tuple I r): Packet X r:=fun z=>∏ i, K (p i) (z i)
def loom (T:Packet I r)(K:Layer I X): Packet X r:= ∑ i:Tuple I r,T i • thread K i
lemma sewn (T:Packet I r)(h:IsSym T)(K:Layer I X): IsSym (loom T K):=by
 intro e z; unfold loom;simp_rw [Finset.sum_apply,Pi.smul_apply,thread];
 rw [← Equiv.sum_comp (Tuple.perm I e)]; apply Finset.sum_congr rfl; intro i _;rw [show T (Tuple.perm I e i)= T i from h e i];congr 1; exact Equiv.prod_comp e (fun j=>K (i j) (z j))

-- finite section eval w. enough to detect all identities. Infinite-sum linear reading costs separate.

variable (C:Y↪ X) (T: Packet I r)(K:Layer I X)
lemma crop_loom : crop C (loom T K)= loom T (fun i z=>K i (C z)):=by unfold loom; rw [crop_sum];ext1 x; rw [Finset.sum_apply, Finset.sum_apply]; rfl
lemma frame_loom [Fintype X](v:X→ℝ) : strum (loom T K) v=strum T (fun i=> (∑ j,K i j*v j)):=by
 unfold strum; simp_rw [tsum_fintype]; unfold loom thread; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sum_mul]; rw [Finset.sum_comm]
 apply Finset.sum_congr rfl;intro i _;change (∑ x:Tuple X r,T i * (∏ j,K (i j) (x j))*noodle v x)= _
 simp_rw [mul_assoc,← Finset.mul_sum]; unfold noodle; simp_rw [← Finset.prod_mul_distrib]; rw [Fintype.prod_sum]
-- only finite sections

def scanL (K:Layer I X)(w:X→ℝ)(i:I):= ∑' x,K i x*w x -- fix
omit [Fintype I] in
lemma gated [Fintype Y](v:Y→ℝ)(i) : (∑ j:Y,K i (C j)*v j)= scanL K (dilute C v) i:=by
 unfold scanL; rw [← C.injective.tsum_eq]; rw [tsum_fintype];apply sum_congr rfl;intro x _;exact congr_arg (K i (C x)* ·) (dilute_here ..).symm
 intro x h; by_contra ht;apply h; dsimp only; rw [dilute_miss C v _ ht,mul_zero]
lemma shoots [Fintype Y](w:Y→ℝ): strum (loom T K) (dilute C w)= strum T (scanL K (dilute C w)):=by rw [crops, crop_loom,frame_loom]; simp_rw [gated]

-- uniform costs over native & orbit metrics
variable (D : Tariff Z)(z:Z)(m:X→Z)
local notation "V" => Premium.uses (Premium.rooted D z) m
lemma lap_road (v:Tuple X r): (V).width v≤ ∏ i,D.road z (m (v i)):=by
 let f(i: Fin r) := D.road z (m (v i)); have hv i : 1 ≤ f i:=D.unit ..;
 apply Premium.width_le
 · apply Tariff.diameter_le _ (Finset.one_le_prod (fun i _=> hv i)); intro a b; by_cases h:a=b
   · subst b;change D.road _ _≤ _;rw [D.own];exact Finset.one_le_prod fun i _=>hv i
   calc
      (D.uses m).road (v a) (v b) ≤ D.road (m (v a)) z * f b:= D.tri ..
      _ ≤ _:=by rw [D.symm (m _), ← Finset.mul_prod_erase _ _ (mem_univ a)];exact mul_le_mul_right (single_le_prod' (fun i _=>hv i) (mem_erase.mpr ⟨Ne.symm h,mem_univ _⟩)) _
 intro i; exact Finset.single_le_prod' (s:=Finset.univ) (f:=f) (fun i _=>hv i) (mem_univ i)
omit [Fintype I] in
lemma thread_cost (i:Tuple I r) {f:ℝ≥0∞}(h:∀ i:I,quota (K i) (fun x:X=>D.road z (m x))≤f):markQ V (thread K i)≤f^r:=by
 apply le_trans _ (show ∏ i:Fin r,f=f^r by simp).le
 apply le_trans _ (prod_le_prod' (f:=fun j=>quota (K (i j)) (fun x:X=>D.road z (m x))) (fun j _=>h _))
 unfold quota;rw [← Gradient.Train.tsum_family]; apply ENNReal.tsum_le_tsum; intro v; rw [Finset.prod_mul_distrib]; change ‖∏ j,K (i j) (v j)‖ₑ*_ ≤ _
 have hχ (α:Finset (Fin r)): ‖∏ j∈α,K (i j) (v j)‖ₑ=∏ j∈α,‖K (i j) (v j)‖ₑ:=by induction α using Finset.induction_on with
  | empty=>simp
  | insert x l h ih=>rw [Finset.prod_insert h,Finset.prod_insert h,enorm_mul,ih]
 exact mul_le_mul' (hχ Finset.univ).le (lap_road D z m v)
lemma loom_cost {f:ℝ≥0∞}(h:∀ i:I,quota (K i) (fun x:X=> D.road z (m x))≤ f): markQ V (loom T K) ≤ (quota T 1)*f^r:=by
 rw [quota_base,tsum_fintype, Finset.sum_mul]; apply le_trans (quota_sum ..)
 exact Finset.sum_le_sum fun i _=> (quota_times ..).trans_le (mul_le_mul_right (thread_cost _ D z m i h) _)
end Loom
end YM.RegulatorIR.Gain
