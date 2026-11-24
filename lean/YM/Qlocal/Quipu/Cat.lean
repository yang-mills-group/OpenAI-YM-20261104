import YM.AllOrder.Floe.Alpine
/-!
 Engine augmentation. In tilted heat one gains two ranks compared to vacuum
 on MARKED delta, which permits actual polynomial insertion projection to close on *same* pole choices. Don't claim support as radial projections; use width sales before organization into offers.

 Algebra directly on aligned full Gaussian, not conditional clipping masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu
open AllOrder AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response GaussianScore
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M J j l r:ℕ} {a C D b:ℝ}
section ink
local notation "X"=> rule α n
lemma tester_l {f g:X→ℝ}{u:(X→ℝ)→ℝ}(h:LinTest X k u)(hf:Rank X k f)(hg:Rank X k g):u (f-g)=u f-u g:= by rw [sub_eq_add_neg, ← neg_one_smul ℝ g, h.add f _ hf (hg.scal _),h.scale _ _ hg]; ring -- inspect Ring
lemma spark_sub (A:Stalk α α){f g v w:rule α n→ℝ}(h:Rank X k f)(H:Rank X k g)(hv:Rank X j v)(hw:Rank X j w): spark A f v-spark A g w= spark A (f-g) v+ spark A g (v-w):= by
   funext x; let t:= (toolA A k v x).2; let h₀: spark A (f-g) v x= spark A f v x-spark A g v x:=tester_l t h H
   have h₁: spark A g (v-w) x= spark A g v x-spark A g w x := tester_l (toolA A j g x).1 hv hw; rw [Pi.sub_apply,Pi.add_apply, h₀,h₁]; ring
lemma net_sub (A:Stalk α α){f g:rule α n→ℝ}(h:Rank X k f)(H:Rank X k g): flicker A n f-flicker A n g=flicker A n (f-g):=by ext1 x; exact (tester_l (tool A (k:=k) x) h H).symm
lemma zero_rank_spark (A:Stalk α α){f:rule α n→ℝ}(h:Rank X 0 f) (g:rule α n→ℝ): spark A f g=0 ∧ spark A g f=0:=by
   have hz i:dab i f=0:=by rw [show f=(fun _=> f 0) from funext fun i=>h.asZero rfl i 0]; unfold dab; unfold diff'; simp; rfl
   unfold spark; simp_rw [hz,mul_zero,zero_mul]; simp
end ink
variable {V:Type} {Λ:V→ℝ} {T:V→ℝ} {Ad:Side→Prop} {W U : ℕ→ℕ→V→Bills α} {A:V→Stalk α α} {f g:V→Bills α}
lemma licensed (ha:0<a) (h:License Ad Λ f a k l) (v:V) (hv:Ad n) : Rank (rule α n) k (f v n):= by
 obtain ⟨F,C,D,hC,hD,H⟩:=h; exact ((H v).fees _ (hD.nonneg v) ha hv).2.1
local notation "H" => License Ad Λ
variable (h:Code Ad A U)(ha:0<a)(hl:CreditF Λ 0 T)(he:∀ i,Belt (A i) a (T i))
   (hp:∀ i≤N,License Ad Λ (U i 0) a (i+2) l) (hg:Code Ad A W)
   (hx:∀ i≤N,License Ad Λ ((W-U) i 0) a i l)
omit h hg hp hx
include ha hl he
local notation "Z"=>chant a N
local notation "Y"=>song l
lemma spark_left (hg:k≤ N)(hH:H f (Z j) r (Y j))(hx: H g (Z j) (k+2) (Y j)): H (fun v n=> spark (A v) (f v n) (g v n)) (Z (j+1)) (r+k) (Y (j+1)):= by
 have hh i := (he i).debt (gestate N ha (show 0≤j from Nat.zero_le j)) le_rfl; have ht:=soprano N ha j; have hz:=soprano N ha (j+1)
 rcases r with _|r; · apply License.adapt (License.null _ hz); intro v n he; exact (zero_rank_spark _ (licensed ht hH _ he) _).1.symm
 refine (hH.join hl ht hh hx hz ?_).squeeze le_rfl (by omega) (by rw [song]; omega); refine (mul_le_mul_of_nonneg_left (show (↑(k+2+1):ℝ)≤(N+3:ℕ) from (by exact_mod_cast (show k+2+1 ≤ N+3 by omega))) hz.le).trans_eq ?_; exact div_mul_cancel₀ _ (by positivity)
lemma spark_right (hg:k≤ N)(hv:r≤N)(hH:H f (Z j) (k+2) (Y j))(hx: H g (Z j) r (Y j)): H (fun v n=> spark (A v) (f v n) (g v n)) (Z (j+1)) (r+k) (Y (j+1)):= by
 have hh i := (he i).debt (gestate N ha (show 0≤j from Nat.zero_le j)) le_rfl; have ht:=soprano N ha j; have hz:=soprano N ha (j+1)
 rcases r with _|r; · apply License.adapt (License.null _ hz); intro v n he; exact (zero_rank_spark _ (licensed ht hx _ he) _).2.symm
 refine (hH.join hl ht hh hx hz ?_).squeeze le_rfl (by omega) (by rw [song]; omega); refine (mul_le_mul_of_nonneg_left (show (↑(r+1+1):ℝ)≤(N+3:ℕ) from (by exact_mod_cast (show r+1+1 ≤ N+3 by omega))) hz.le).trans_eq ?_; exact div_mul_cancel₀ _ (by positivity)
include h hg hp hx
lemma revenue' (hk:k≤N) : H (W k 0) a (k+2) l := by
    apply License.adapt (License.add ((hx _ hk).squeeze le_rfl (by omega : k≤ k+2) le_rfl) (hp k hk) ha); intro i n _; exact sub_add_cancel ..
lemma golden (i:ℕ)(hk:k≤N) : H ((W-U) k i) (Z i) k (Y i):= by
   induction i using Nat.strong_induction_on generalizing k with
   | h i ih=>
     rcases i with _|i; exact hx k hk
     rcases i with _|i; · apply License.adapt (License.null _ (soprano N ha (0+1))); intro v n hn; change 0= W k 1 v n-U k 1 v n; rw [h.one _ _ _ hn,hg.one _ _ _ hn,sub_self]
     let F:=W-U; have ht:=soprano N ha i; have hq:= soprano N ha (i+1); have hq':= soprano N ha (i+1+1); have hr (k:ℕ) (hh:k ≤ N) (j:ℕ) (hv:j ≤ i): H (F k j) (Z i) k (Y i):= (ih j (by omega) hh).squeeze (gestate N ha hv) le_rfl (gesture l hv)
     have hup (k:ℕ) (hh:k ≤ N) (j:ℕ) (hv:j ≤ i): H (U k j) (Z i) (k+2) (Y i):= (aqua h hl ha he l hp j hh).squeeze (gestate N ha hv) le_rfl (gesture l hv)
     have hW (k:ℕ) (hh:k ≤ N) (j:ℕ) (hv:j ≤ i):H (W k j) (Z i) (k+2) (Y i):=(aqua hg hl ha he l (fun i hh=> revenue' h ha hl he hp hg hx hh) j hh).squeeze (gestate N ha hv) le_rfl (gesture l hv)
     let X(r j:ℕ)(v:V)(n:Side):= spark (A v) (F (k-r) (i-j) v n) (W r j v n)+spark (A v) (U (k-r) (i-j) v n) (F r j v n)
     have hh (r:ℕ) (hv:r ≤  k) (j:ℕ) (hj:j ≤ i): H (X r j) (Z (i+1)) k (Y (i+1)):= License.add ((spark_left ha hl he (hv.trans hk) (hr (k-r) (by omega) (i-j) (by omega)) (hW r (by omega) j hj)).squeeze le_rfl (by omega) le_rfl) ((spark_right ha hl he (by omega) (by omega) (hup (k-r) (by omega) (i-j) (by omega)) (hr r (hv.trans hk) j hj)).squeeze le_rfl (by omega) le_rfl) hq
     let X1 (r:ℕ)(v:V)(n:Side):= ∑ j∈range (i+1), X r j v n
     have hX(r:ℕ)(hr:r ≤  k): H (X1 r) (Z (i+1)) k (Y (i+1)):= License.pile _ _ (fun j hj=> hh r hr j (Nat.le_of_lt_succ (mem_range.mp hj))) hq
     let X' (v:V)(n:Side):= flicker (A v) n (F k i v n); have hJ:H X' (Z (i+1)) k (Y (i+1)) := ((hr k hk i le_rfl).furnish hl ht (fun j=> (he j).debt (gestate N ha (show 0  ≤  i from Nat.zero_le i)) le_rfl)).squeeze (gestate _ ha (by omega)) (by omega) (by rw [song];omega) -- arg order
     refine License.adapt ((License.add (License.pile (range (k+1)) X1 (fun r hr=>hX r (Nat.le_of_lt_succ (mem_range.mp hr))) hq) hJ hq).scale ((↑(i+2:ℕ):ℝ)⁻¹) |>.squeeze (gestate _ ha (by omega)) le_rfl (gesture l (by omega))) ?_
     intro v n hn;
     dsimp only [Pi.sub_apply]; rw [h.pact _ _ _ _ hn, hg.pact _ _ _ _ hn, ← smul_sub]; refine congr_arg _ ?_; unfold X'; rw [add_sub_add_comm, net_sub _ (licensed ht (hW k hk i le_rfl) v hn) (licensed ht (hup k hk i le_rfl) v hn)]; refine congr_arg₂ (· + ·) ?_ rfl; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro r hl; have hh':=Nat.le_of_lt_succ (mem_range.mp hl); rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j hj=>?_ ; have hj':=Nat.le_of_lt_succ (mem_range.mp hj); exact (spark_sub (A v) (licensed ht (hW (k-r) (by omega) (i-j) (by omega)) v hn) (licensed ht (hup (k-r) (by omega) (i-j) (by omega)) v hn) (licensed ht (hW r (by omega) j hj') v hn) (licensed ht (hup r (by omega) j hj') v hn)).symm
lemma rents_delta (hk:k≤N): H ((snapshot W - snapshot U) k) (Z (3*N)) k (Y (3*N)):= by
 refine License.adapt (License.pile (range (3*k+1)) ((W-U) k) (fun i hi=>(golden h ha hl he hp hg hx i hk).squeeze (gestate _ ha ( (Nat.le_of_lt_succ (mem_range.mp hi)).trans (by omega))) le_rfl (gesture l ((Nat.le_of_lt_succ (mem_range.mp hi)).trans (by omega)))) (soprano N ha _)) (fun i n hn=> Finset.sum_sub_distrib (f:=fun j=> W k j i n) (g:=fun j=> U k j i n)) -- signature explicit? 
end YM.Qlocal.Quipu
