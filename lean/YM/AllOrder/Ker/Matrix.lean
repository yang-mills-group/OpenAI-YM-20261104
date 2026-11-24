import YM.AllOrder.Ker.Spine
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker.Start
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Spine Matrix Next.Fluctuations
open scoped BigOperators Topology Classical ContDiff
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{M N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "J[" n "]"=> Leaf n (Lobby P K G)
local notation "X[" n "]"=> Leaf n (Coarse G)
local notation "Y[" n "]"=> Leaf n (RealSlice.Vertical G P K)
variable (p:Clip)(R:PathData G)
abbrev ΛN (F:Mat n (Lobby P K G) (Lobby P K G) 1) : Matrix Y[n] Y[n] ℝ := (headMatrix F).submatrix (Primitives.TwoWave.peg (Coarse G)) (Primitives.TwoWave.peg _)
def seedT (n:Side):= billed P K (classicalT P K R p) 1 n
def pulse (n:Side):= ΛN P K (seedT P K p R n)
def green (n:Side): Mat n (RealSlice.Vertical G P K) (RealSlice.Vertical G P K) 1:=mpack (pulse P K p R n)⁻¹
local notation "B[" n "]"=> pulse P K p R n
local notation "M[" n "]"=> green P K p R n
variable {a C Λ:ℝ} (Q:Push.Uniform.Before G a C P.J K N)(h:R.Bounds p a C Λ)(hn:Ad G P K n)
local notation "L"=> Q.tables p P
include Q h hn
-- 
lemma blocks : let F:=classicalT P K R p n; ContDiffAt ℝ ω F 0 ∧ 0<(Push.Uniform.block F 0).det ∧ Sealed (address T[n] G ∘ Sum.inr) (L).rate (Push.Uniform.block F 0)⁻¹ ((L).gap/2/2)⁻¹:= by
   have he:= (Q.receipt T[n] (label S[n]) h hn rfl rfl).1; have hu:= he.priced_inverse 0 (mem_closedBall_self he.reserveH_pos.le); exact ⟨(he.born _ (mem_ball_self he.pos_r)).1,hu.1,hu.2.1⟩
lemma bump (i j:J[n]): let f:=classicalT P K R p; let B:= mapper P K G (enough P K hn); (headMatrix (seedT P K p R n)) i j = entry (f n) 0 ![B i,B j] := by
   intro f B; let F:= f n; let E:= redesk B; let g:=headMatrix (seedT P K p R n); rw [headMatrix_at]; unfold seedT billed extractF tax; rw [dif_pos (enough P K hn)]; change iteratedFDeriv ℝ 2 (F ∘ E.toContinuousLinearMap) 0 _=_; let L':= E.toContinuousLinearMap; rw [Next.Foundations.jets_linear L' ((blocks P K p R Q h hn).1.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; refine congr_arg (⇑(iteratedFDeriv ℝ 2 F 0)) (funext fun k=>?_); fin_cases k; exact desk_spot ..; exact desk_spot ..
lemma pulse_p : let A:=classicalT P K R p n; let e:= insider P K G (enough P K hn); pulse P K p R n=(block A 0).submatrix e e:= by
   intro A e; let B:=mapper P K G (enough P K hn); ext i j; rw [Matrix.submatrix_apply]; let H:= block A 0; unfold pulse; rw [ΛN, Matrix.submatrix_apply,bump P K p R Q h hn]; let he:= ((block_hermitian (blocks P K p R Q h hn).1).apply (e i) (e j)); rw [star_trivial] at he; exact he -- sign
lemma pulse_det : 0<(B[n]).det:=by rw [pulse_p P K p R Q h hn,det_submatrix_equiv_self]; exact (blocks P K p R Q h hn).2.1
lemma move_cost (i j:Y[n]): |(B[n])⁻¹ i j| ≤
    ((L).gap/2/2)⁻¹ * Real.exp (L).rate * Real.exp (-(L).rate * separation i.1 j.1):=by
   let Y':=L; let t:= Y'.rate; let v:= ((Y').gap/2/2)⁻¹; let M':=insider P K G (enough P K hn); let x (i:Y[n]):= address T[n] G (Sum.inr (M' i)); let W:= block (classicalT P K R p n) 0; rw [pulse_p P K p R Q h hn, Matrix.inv_submatrix_equiv, Matrix.submatrix_apply]; change |W⁻¹ _ _| ≤ v*Real.exp t*_
   rw [mul_assoc, ← Real.exp_add]; have h0:0<t:= (Q.full_pack T[n] (label S[n]) h hn rfl rfl).2.2.2.2.2.2.1; have hZ:0<(L).gap:=(Q.receipt T[n] (label S[n]) h hn rfl rfl).1.pos_m
   refine ((blocks P K p R Q h hn).2.2 (M' i) (M' j)).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (inv_pos_of_pos (half_pos (half_pos hZ))).le)
   change -t*↑(separation (x i) (x j)) ≤ t+-t*separation i.1 j.1; have ht: separation i.1 j.1 ≤ separation (x i) (x j)+1:= priceG P K (enough P K hn) (Primitives.TwoWave.peg (Coarse G) i) (Primitives.TwoWave.peg (Coarse G) j); have he : (separation i.1 j.1:ℝ) ≤ separation (x i) (x j)+(1:ℝ):=by exact_mod_cast ht
   nlinarith only [he,mul_le_mul_of_nonneg_left he h0.le]

-- across
omit hn
def stairC := ((L).gap/2/2)⁻¹ * Real.exp (L).rate
lemma cap_green (hB:P.Branches K G) : ∃ F : Fan (RealSlice.Vertical G P K) (RealSlice.Vertical G P K) 1, Cap F (small_a (L).rate) (stairC P K p Q * boltC 1 (L).rate) ∧ ∀ n:Side, Ad G P K n→ M[n]= pieces F n:=by
   let I:=Ad G P K; let f:= classicalT P K R p; obtain ⟨d,H⟩:=dock_larger P K hB; let T n:=seedT P K p R n; let t:Side:=⟨d+1,by omega⟩; have ht:= Q.full_pack T[t] (label S[t]) h (H t (by show d≤d+1; omega)) rfl rfl; let v:= stairC P K p Q
   have hz(n:Side)(hi:I n): ContDiffAt ℝ ω (f n) 0:= (blocks P K p R Q h hi).1; let hG:= billed_keeps P K I f (fun _=> enough P K) (fun _ n m W _ _ x=> (walks P K W).appraisal K x (label _) p R) hz 1
   have hu(m n:Side)(hm:I m)(hn:I n)(N:ℕ)(W:Window n m N)(h':Same (T n) (T m) W): Same M[n] M[m] W := by
      have he:= Shingle.flip (R:=pulse P K p R m) (T:=pulse P K p R n) (π:=BookM W (RealSlice.Vertical G P K)); have hl:= fielding W (headMatrix (T n)) (headMatrix (T m)); rw [he_pack,he_pack] at hl; exact (fielding ..).1 (he (smol W (hl.2 h') Sum.inr (Sum.inr_injective)) (pulse_det P K p R Q h hm).ne' (pulse_det P K p R Q h hn).ne')
   have he:0<v:=mul_pos (inv_pos_of_pos (half_pos (half_pos ht.2.1))) (Real.exp_pos _);
   refine obtain_fan ⟨d,H⟩ ⟨fun n hn w=> ?_,fun n m hm hn t hM=> hu m n hm hn _ _ (hG.multiple n m hm hn t hM)⟩ (fun n hn i t=> ?_) ht.2.2.2.2.2.2.1 he.le; · exact (stationed M[n] w).1 (hu n n hn hn _ _ ((stationed (T n) w).2 (hG.same n hn w)))
   rw [Fin.sum_univ_one]; exact move_cost P K p R Q h hn i (t 0)
end YM.AllOrder.Ker.Start
