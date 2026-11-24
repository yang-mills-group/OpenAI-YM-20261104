import YM.AllOrder.Ker.Transfer
import YM.Work.E04
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Liquid
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Migrations
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker
open Lattice Laurent Bloch Matrix Complex RG Push.Uniform Precision Push
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Primitives.TwoWave Primitives.TwoWave.RealSlice Further.PhysicalPeriodLimitF933 Shingle Macrame
open scoped BigOperators Topology Classical ContDiff
variable {n m : Side} {α β : Type} [Fintype α] [Fintype β] {k M : ℕ}
namespace Start
open Work.F03 Next.Fluctuations Gauge Tree Pressure Jacobi Finset Bid Exterior Filter Metric
variable (P:Patch)(K:KernelChoices){G:Gauge}
set_option quotPrecheck false
abbrev Lobby (G:Gauge):= Coarse G⊕RealSlice.Vertical G P K -- inspect namespace
abbrev prom (G:Gauge)(hn:3≤n.val) : rule (Lobby P K G) n≃L[ℝ] Positions (Joint (trees P K n) G):= redesk (mapper P K G hn)
lemma walks (W:Lace (show (below P n).val=(n : Side).val*P.L.val from rfl) (show (below P m).val=(m : Side).val*P.L.val from rfl) M): W.Fitted (trees P K n) (trees P K m):= by
 constructor; intro x; change (model P K).up ((shores P three).assemble (0,W.R.residue x)) = (model P K).up ((shores P three).assemble (0,W.r.residue (W.high.cut x))); rw [W.room]
lemma nests (W:Lace (show (below P n).val=(n : Side).val*P.L.val from rfl) (show (below P m).val=(m : Side).val*P.L.val from rfl) M) (hm:3≤m.val)(hn:3≤n.val)(x:Leaf m (Lobby P K G)): mapper P K G hn (BookM W.low _ x)=(walks P K W).bores (mapper P K G hm x):= by
  rcases x with ⟨x,a|b⟩; · rfl
  apply congr_arg Sum.inr; apply Prod.ext <;> try rfl; -- inspect
  apply Subtype.ext; exact Prod.ext (W.regions ..).symm rfl
lemma speaking (W:Lace (show (below P n).val=(n : Side).val*P.L.val from rfl) (show (below P m).val=(m : Side).val*P.L.val from rfl) M) (hm:3≤m.val)(hn:3≤n.val)(x): prom P K G hm (convey W.low x)=prom P K G hn x ∘ (walks P K W).bores:= by
  funext i; let U:=mapper P K G hm; let B:=mapper P K G hn; obtain ⟨i,rfl⟩:= U.surjective i; change x (BookM W.low _ (U.symm (U i)))= x (B.symm _); rw [U.symm_apply_apply, ← show B (BookM W.low _ i)=_ from nests P K W hm hn i, B.symm_apply_apply]

-- purchase mechanism applied to any invoice with price already paid
lemma live (hn:3 ≤ n.val)(x:Leaf n (Lobby P K G)): let B:= mapper P K G hn; (shores P n).parent (address (trees P K n) G (B x))=x.1:= by
 intro B; rcases x with ⟨x,a|b⟩; · exact Ratio.embed_parent ..
 exact Ratio.assemble_parent ..
lemma priceG (hn:3≤n.val)(x y:Leaf n (Lobby P K G)): let B:= mapper P K G hn; separation x.1 y.1 ≤ separation (address (trees P K n) G (B x)) (address (trees P K n) G (B y))+1:= by intro B; rw [← live P K hn x, ← live P K hn y]; exact Work.E04.parent_separation ..

variable (Ad₀: Side→Prop)(F:(n:Side)→ Positions (Joint (trees P K n) G)→ℝ) (H:∀ n,Ad₀ n →3≤n.val)
variable (hm:∀ M n m,∀ W:Lace (show (below P n).val=(n : Side).val*P.L.val from rfl) (show (below P m).val=(m : Side).val*P.L.val from rfl) M, Ad₀ n → Ad₀ m → ∀ x:Positions (Joint (trees P K n) G), F m (x ∘ (walks P K W).bores)=(M:ℝ)*F n x)
variable (hf:∀ n,Ad₀ n→ContDiffAt ℝ ω (F n) 0) {a C:ℝ}
def tax (k:ℕ) (n:Side): Page (Leaf n (Lobby P K G)) (k+1) := if h:3≤n.val then iteratedFDeriv ℝ (k+1) (F n ∘ prom P K G h) 0 else 0
def billed (k:ℕ) (n:Side): Mat n (Lobby P K G) (Lobby P K G) k := extractF (tax P K F k n)
include hf H
lemma seat_cost (A:0≤a)(hz:0≤C) (N k:ℕ)(hk:k+1 ≤ N)(ht:Ad₀ n)(he: Scatter (address (trees P K n) G) a N (F n) 0 C): Room (billed P K F k n) a (C*Real.exp (a*(k:ℝ))) := by
  let L:= mapper P K G (H n ht); let B:= redesk L; intro i w; let v:Fin (k+1)→Leaf n (Lobby P K G):= Fin.cons i w; have h:= he (k+1) hk (L ∘ v) 0; let x:=fun j=> address (trees P K n) G (L (v j)); let S : ℕ:=spanSites (address (trees P K n) G) (x 0) (L ∘ v)
  have ha : billed P K F k n i w = entry (F n) 0 (L ∘ v) := by
     unfold billed extractF tax; rw [dif_pos (H n ht)]; change iteratedFDeriv ℝ (k+1) (F n ∘ B.toContinuousLinearMap) _ _ = _; rw [Next.Foundations.jets_linear _ ((hf n ht).of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; exact congr_arg (⇑(iteratedFDeriv ℝ (k+1) (F n) 0)) (funext fun j=>desk_spot ..)
  rw [ha,← Real.norm_eq_abs,mul_assoc,←Real.exp_add]; refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hz)
  let d:=∑ j:Fin k,separation i.1 (w j).1; change -a*(S:ℝ) ≤ a*k+-a*d; have hh : d ≤ S+k:= calc
    _ ≤ ∑ j:Fin k, (separation (x 0) (x j.succ)+1):=Finset.sum_le_sum fun j _=> show separation (v 0).1 (v j.succ).1 ≤ _ from priceG P K (H n ht) _ _
    _ = S+k:= by unfold S spanSites; rw [Fin.sum_univ_succ,Finset.sum_add_distrib]; simp [x,L] -- edit
  have hu :(d:ℝ)≤ S+k:=by exact_mod_cast hh
  nlinarith
include hm
lemma billed_keeps (k:ℕ) : Keep (billed P K F k) Ad₀ := by
  have he(n m:Side)(a:Ad₀ n)(b:Ad₀ m) (d:ℕ)(W:Lace (show (below P n).val=(n : Side).val*P.L.val from rfl) (show (below P m).val=(m : Side).val*P.L.val from rfl) d): pilots W.low (tax P K F k n) (tax P K F k m):= by
     unfold tax; rw [dif_pos (H n a),dif_pos (H m b)]; refine flight W.low ((by rw [map_zero]; exact hf n a : ContDiffAt ℝ ω (F n) (prom P K G (H n a) 0)).comp (f:=prom P K G (H n a)) 0 (prom P K G _).contDiff.contDiffAt) ?_ (Eventually.of_forall fun i=>?_)
     · exact (show ContDiffAt ℝ ω (F m) (prom P K G (H m b) 0) from by rw [map_zero]; exact hf m b).comp (f:=prom P K G _) 0 (prom P K G _).contDiff.contDiffAt
     simp only [Function.comp_apply]; rw [speaking P K W _ (H n a)]; exact hm _ n m W a b _
  have hs(n:Side)(a:Ad₀ n)(w:Site n):= he n n a a 1 (Macrame.Lace.hub w (show 2 ≤ n.val from le_trans (by norm_num) (H n a)))
  refine ⟨fun n a=>pilots.still (hs n a),fun n m b a t ht=> ?_⟩
  exact cooks _ (pow_pos (Nat.pos_of_mul_pos_left (show 0<n.val*t from ht ▸ m.property)) _) (he n m a b (t^4) (Macrame.Lace.project ht (show 2 ≤ n.val from le_trans (by norm_num) (H n a)))) (hs m b)
end Start
end YM.AllOrder.Ker
