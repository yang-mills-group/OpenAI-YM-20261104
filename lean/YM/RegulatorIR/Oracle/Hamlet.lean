import YM.RegulatorIR.Oracle.Quota

/-! LOCAL primitive universal roll cost under arbitrary Scale through
p (needs costs only to p on β). Hartree dropped q=0 Price.Mask remains no.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {G:Gauge} {X Y A B I V: Type} {α σ Ω Ω' δ δ' l s P:ℝ} {u p q k i j:ℕ} {n t f:Side}

section fibers
lemma earned_drums (T:X→Ranked I)(s:Finset X) (h:∀ i∈s,∀ k, Bounded (T i k)) (u p): Prim.drums (∑ i∈s,T i) p u=∑ i∈s,Prim.drums (T i) p u:=by
 unfold drums; rw [Finset.sum_comm (s:=s)]; apply Finset.sum_congr rfl;intro i hi; unfold Prim.strum; simp_rw [Finset.sum_apply,sum_mul]; exact Summable.tsum_finsetSum (fun j hj=> summable_of_hasFiniteSupport ((h j hj i).subset (fun i hi=>left_ne_zero_of_mul hi)))
lemma drums_scale (T:Ranked I) (c:ℝ)(v p):drums (c•T) p v=c*drums T p v:=by unfold drums;rw [mul_sum]; exact sum_congr rfl fun _ _=> strum_tilt ..
lemma hardy (T:Ranked I)(h:Within u T)(x:I→ℝ)(hp:u≤p): drums T u x=drums T p x:=by
 apply sum_subset (range_mono (by omega)); intro j hj he; have hz:T j=0:=by by_contra! hx; apply he;exact mem_range.mpr (by have hc:=h j hx;omega)
 rw [hz,strum_zero]
lemma sB (T:Packet X p) (h:Bounded T)(c:ℝ): Bounded (c • T):= (show (support T).Finite from h).subset (fun _ hi=> right_ne_zero_of_mul hi)
variable {S:StepData n f}(C:S.patch.Branches S.kernel G)

-- bias t^2 integrand $β=1`, keep all scale degrees incl rank 2. linear assembly any Scale. $at (q)$. Need no pp+2 BudgetPresents (uses clipping). 
def standby (e:Edge Cover): Orders (KFoot G):= ((locally S C Clocks.flat e).some.issues (-1) 0).choose
lemma boosted (e:Edge Cover): Lab 0 (-1) (opi S Clocks.flat e) (standby C e):=((locally S C Clocks.flat e).some.issues (-1) 0).choose_spec
lemma pencil (z:Edge Cover)(p:Fin 2) : standby C z p.val=0:=by
 let V:= standby C z;have hf:= boosted C z
 fin_cases p
 · exact hf.awake
 change V 1 = _
 have hx : Within (1+0) (0 : Ranked (KFoot G)):=fun p a=>False.elim (a rfl)
 refine Prim.guessed (hf.scope_ _) hx (hf.smooth _) (fun _=>symmetric_zero) (fun x=>?_)
 rw [hf.figures x (by norm_num)]; let f:= flank (opi S Clocks.flat z (G:=G)) x
 have hg: coeff 1 (tale f) = 0:= grows_sq (f:=f) ((locally S C Clocks.flat z).some.smooth_v _) (fun _=> mul_nonneg (mul_nonneg (Clocks.flat.forward _) S.kernel.penalty_pos.le) (G.price_range _).1) (by unfold f flank;rw [zero_smul]; exact opi_zero S C Clocks.flat _ _) 1 (by omega)
 simp [drums,strum]; exact hg
-- charges beyond e.
variable (T:Binding.Scale)
def biases (j:ℕ):ℝ:= PowerSeries.coeff j (tale T.beta)
def laterBias (j:ℕ) (V:Orders I) := ∑ d∈ Finset.HasAntidiagonal.antidiagonal j, biases T d.1 • V (d.2+2)

include C
lemma milk {x:Edge Cover}{W:Orders (KFoot G)}(h : Lab 2 (-1) (opi S T x) W) (j:ℕ) (hv:0<j) : W j=laterBias T j (standby C x):=by
 let V:= standby C x; let f:= HasAntidiagonal.antidiagonal (j+2); let k:= HasAntidiagonal.antidiagonal j; let φ (d:ℕ×ℕ):=biases T d.1 • (V d.2)
 have ht:= boosted C x
 have he : (∑ d∈f,φ d) = laterBias T j V:=by
    unfold laterBias; symm
    let t:=fun z:ℕ×ℕ=> (z.1,z.2+2)
    apply Finset.sum_of_injOn t
    · intro i _ j _ h; obtain ⟨p,hv⟩:=Prod.mk.inj h; exact Prod.ext p (add_right_cancel hv)
    · intro i hi; exact mem_antidiagonal.mpr (show i.1+(i.2+2)=j+2 from by have h:= mem_antidiagonal.mp (show i∈ k from hi);omega)
    · intro i hi h; by_cases ht:2 ≤ i.2
      · have he:(i.1,i.2-2)∈k:=by rw [mem_antidiagonal]; have hp:= mem_antidiagonal.mp (show i∈f from hi);simp only;omega
        have hg:t (i.1,i.2-2)=i:=Prod.ext rfl (Nat.sub_add_cancel ht)
        exact (h ⟨_,he,hg⟩).elim
      unfold φ; rw [show V i.2 = _ from pencil C x ⟨_,lt_of_not_ge ht⟩,smul_zero]
    intro i hi; rfl
 rw [← he]
 have hP :Within (j+2) (∑ d∈f, φ d):=by
    intro i hi; rw [Finset.sum_apply] at hi; obtain ⟨w,hw,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero hi; have hp : V w.2 i≠0:= fun hx=>h (by change (biases T w.1) • V w.2 i=_;rw [hx,smul_zero]); have he:= ht.scope_ w.2 i hp; have hv:= mem_antidiagonal.mp hw;omega
 apply guessed (h.scope_ _) hP (h.smooth _)
 · intro v;rw [Finset.sum_apply]; exact symmetric_sum (fun i _=> symmetric_scale (ht.smooth i.2 v) _)
 intro t; rw [h.figures t hv, earned_drums φ f]
 swap; exact fun i _ k=> sB _ (ht.sized i.2 k) _
 let g:= flank (opi S Clocks.flat x) t; let W:=tale g
 have hs: flank (opi S T x) t=T.beta*g:=by ext1 i;change T.beta i* _ * _ = T.beta i*(1*S.kernel.penalty*_); ring
 rw [hs,tale_mul T.near (show ContDiffAt ℝ  (↑(⊤:ℕ∞)) g 0 from (locally S C _ x).some.smooth_v t), coeff_mul,Finset.mul_sum]
 apply sum_congr rfl;intro w hw; rw [show φ w= _ from rfl]; unfold φ; rw [drums_scale];
 by_cases he: w.2>0
 · have hx : drums (V w.2) (j+2) t= -1*coeff w.2 W:=by
      rw [← hardy (V w.2) (ht.scope_ w.2)]; exact ht.figures t he; have hp:=mem_antidiagonal.mp hw;omega
   rw [hx];exact mul_left_comm ..
 rw [show w.2=0 by omega, show V 0 = _ from ht.awake,show coeff 0 (tale g)=0 from ?_]
 · simp [drums,strum]
 rw [tale_base]; unfold g flank;rw [zero_smul];exact opi_zero S C Clocks.flat ..
end fibers
end YM.RegulatorIR.Oracle
