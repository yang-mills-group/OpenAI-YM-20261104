import YM.XSpace.Uptown
import YM.XSpace.Grades

/-!
# A local gauge-invariant cap is really a physical label

Factor through the on-shell space of the calibrated stencil fields. Need engineering-
triangular at each entry, not grade identity in any mixture beyond input weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Bracket
open Function Set Filter Lows Scale Mu Uptown Normalize Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Contraction Finsupp
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{d n:ℕ}

private def oneStep (A:TaylorTower G) : (i:ℕ)→ Tune i G.Color
| 0=>0
| i+1 => roll (A i)
def seat (d:ℕ)(A:TaylorTower G):Hat G d:= fun i=> oneStep A i.val
def cube (B:Hat G d):TaylorTower G:= fun i=> if h:i+1<d+1 then ink (B ⟨i+1,h⟩) else 0
lemma seats (B:Hat G d): seat d (cube B)= radial G d B:=by
  unfold radial; ext1 i; change oneStep _ i.val= assay i.val (B i); rcases i with ⟨i,h⟩; cases i with
  | zero=> rfl
  | succ i=> change oneStep _ (i+1)=_; rw [oneStep,cube,dif_pos h];rfl
-- Spell fragment for physical shadows
def aPoint (n:ℕ):= Module.finBasis ℝ (Tune n G.Color)
private def aSymbolM :(n:ℕ)→ Fin (Module.finrank ℝ (Tune n G.Color)) → WickPol G
| 0, _=>0
| i+1,p=> Maxwell.symbol _ (((aPoint (G:=G) (i+1)).coord p).comp (roll (G:=G) (d:=i)))

private lemma right_leg (n:ℕ)(p): IsWeightedHomogeneous scaleW (aSymbolM (G:=G) n p) (1+n):=by cases n with
  | zero=> exact isWeightedHomogeneous_zero ..
  | succ i=> rw [aSymbolM, show 1+(i+1)=i+2 by omega]; exact symbol_hom _ (·+2)
def amber (i:Index G d) := aSymbolM i.1.val i.2
def archive (d:ℕ) : Cap G d →ₐ[ℂ] WickPol G := aeval amber
lemma links (i:Index G d) : IsWeightedHomogeneous scaleW (archive d (X i)) (coin i):=by rw [archive,aeval_X]; exact right_leg _ _
lemma dicto (A: TaylorTower G)(q:Cap G d) : probe A (archive d q)= view (seat d A) q:=by
  suffices h:(probe A).comp (archive d)=view (seat d A) from DFunLike.congr_fun h q; ext1 i; rw [AlgHom.comp_apply,archive,aeval_X,view,aeval_X]; rcases i with ⟨⟨i,h⟩,p⟩; unfold bank; rw [Pi.basis_repr]; change probe A (aSymbolM i p)= ↑((aPoint (G:=G) i).repr (oneStep A i) p); cases i with | zero=> simp only [aSymbolM,oneStep,map_zero,Finsupp.zero_apply, Complex.ofReal_zero] | succ i=> rw [aSymbolM,symbol_test];rfl
lemma dictoB (B:Hat G d)(q:Cap G d): probe (cube B) (archive d q)= view B (cross (radial G d) q):= by rw [dicto,seats,crossing]
lemma amber_bound {q: Cap G d}(h:q∈Load G d n): archive d q∈ weightBound scaleW n:= transfers coin scaleW _ links q h
lemma cutback (q:Cap G d) (n): trunc scaleW n (archive d q)=archive d (trunc coin n q):=by
  unfold trunc; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> commuting _ _ (archive d) links q i

-- extracting coeff via leading limit at zero spacing.
local notation "L" => nhdsWithin (0:ℝ) (Ioi 0)

private lemma unit_tick (k:ℕ)(v B:ℕ)(f:ℕ→ℂ)(h:∀ i:ℕ,i<k→f i=0)(ht:k≤B) (x:ℂ)(H:Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^k*∑ i∈Finset.range (B+1),(t:ℂ)^i*f i) L (𝓝 x)): f k=x:=by
  apply tendsto_nhds_unique _ H; simp_rw [Finset.mul_sum]; let p (i:ℕ):ℂ:= if i=k then f i else 0; rw [← show (∑ i∈Finset.range (B+1),p i) = f k by simp [p, ht]]
  apply tendsto_finsetSum; intro i _; by_cases hB:k ≤ i; swap; · simp only [h i (Nat.lt_of_not_ge hB),mul_zero,p,ite_self]; exact tendsto_const_nhds
  have h₀: Tendsto (fun t:ℝ=>(t:ℂ)) L (𝓝 0):= by simpa using (Complex.continuous_ofReal.tendsto 0 |>.mono_left (show L≤ _ from nhdsWithin_le_nhds))
  have hy:((0:ℂ)^(i-k)*f i)=p i := by by_cases H:i=k; simp [p,H]; simp [p,H, Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hB (Ne.symm H))]
  rw [← hy]; refine ((h₀.pow (i-k)).mul_const _).congr' ?_; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht; have he:(t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt ht); rw [show (t:ℂ)^i=(t:ℂ)^k*(t:ℂ)^(i-k) by rw [← pow_add]; congr 1; omega,inv_pow]; field_simp
lemma resurrect (v:Cap G d)(n:ℕ)(p:WickPol G)(h:∀ X: TaylorTower G,Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^n*view (orchestra d t (seat d X)) v) L (𝓝 (probe X p))) : trunc scaleW n (archive d v)=p:=by
  rw [cutback]; apply Maxwell.equalPol _ _; intro x; rw [dicto,trunc,LinearMap.sum_apply,map_sum];
  specialize h x; set u:=seat d x; obtain ⟨B,hB⟩:=cap_known coin v; set N:=max n B; set f:= fun i:ℕ=> view u (Cut coin i v); set z:=probe x p
  simp_rw [uncut _ _ (higher coin (le_max_right n B) hB)] at h
  have he(k:ℕ)(hk:k<n): Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^k*∑ i∈Finset.range (N+1),(t:ℂ)^i*f i) L (𝓝 0):= by
    have he:= ((Complex.continuous_ofReal.tendsto 0|>.mono_left (show L≤_ from nhdsWithin_le_nhds)).pow (n-k)).mul h
    rw [Complex.ofReal_zero, zero_pow (Nat.sub_ne_zero_of_lt hk),zero_mul] at he; refine he.congr' ?_; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht; clear he h; have he:(t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    change (_:ℂ)*( (t:ℂ)⁻¹^n * (∑ i∈Finset.range (N+1),(t:ℂ)^i*f i))=_; rw [← mul_assoc]; congr 1; rw [inv_pow,inv_pow,show (t:ℂ)^n=(t:ℂ)^k*(t:ℂ)^(n-k) by rw [← pow_add]; congr 1; omega]; field_simp
  have hx(i:ℕ)(hi:i<n): f i=0:=by induction i using Nat.strong_induction_on with | h i ih=> exact unit_tick i i N f (fun j hj=> ih _ hj (lt_trans hj hi)) (le_trans hi.le (le_max_left ..)) _ (he i hi)
  change (∑ i∈ Finset.range (n+1),f i)=z; rw [Finset.sum_range_succ, Finset.sum_eq_zero (s:=Finset.range n) (fun i hi=>hx i (Finset.mem_range.mp hi)),zero_add]; exact unit_tick n n N f hx (le_max_left ..) _ h
end YM.XSpace.Bracket
