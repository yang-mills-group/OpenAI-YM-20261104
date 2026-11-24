import YM.FVAAlt2.Home.Poses
/-!
# Regulator geometry. From the ACTUAL LPT schedule `_∈ origins` at each
 q,m and every compact demand provide genuine two-cutoff IR/spacing inputs
 of `MS.Tide` and `Dial.Trial`. Cost holds uniformly on every compact subset
 of `YM.conf n`. Allows even points arising at (different) radii/measuring
 conventions, in this precise physical coordinate/profile, if meeting this
 bound. No extra exterior cluster-size assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Function Finset Filter Topology Lattice
open Set Metric MeasureTheory
open MS MS.Koszul MS.Menus MS.Book MS.Theater MS.Tone MS.Vista MS.Fleet MS.High MS.Tide MS.Orbit MS.Rake
open Extraction
open Pert.Orb PertExtension PertExtension.LatticePT
open Real
open scoped BigOperators Topology ContDiff
variable {d:ℕ}{q:ℕ+}{u:Side} {n j:ℕ}
local notation "V" => Native q n
local notation "ε"=> epsilon q n
variable (q n)
def lengthP (q:ℕ+)(n:ℕ): Side:= ⟨4*(q.val^(n+1)*q.val^(n^2)),by positivity⟩
lemma recorded: periodN (lengthP q n) = LatticePT.side q n:= by apply Subtype.ext; change 2*(4*(q.val^(n+1)*q.val^(n^2)))= nativePeriod q n; unfold nativePeriod; ring_nf
lemma buf_eval (q:ℕ+)(n:ℕ): (LatticePT.side q n).val=8 * buffer q n:= by
 unfold buffer; change nativePeriod q n= 8*(nativePeriod q n /8); unfold nativePeriod; rw [mul_assoc,Nat.mul_div_cancel_left ..]; decide -- orientation
lemma ticks_one (q:ℕ+)(n:ℕ): 0<(LatticePT.side q n).val:= (side q n).pos
variable {q n} {K:Set (Points d)}
lemma center_bound{x:V} (h:x∈origins q n): 8*pdist x≥(LatticePT.side q n).val ∧ 4*pdist x≤(LatticePT.side q n).val := by
 obtain ⟨_,h⟩:= Finset.mem_filter.mp h; have ht:=buf_eval q n; have hp:=ticks_one q n; let y(i:Axis):ℤ:= ( (x i).val :ℤ ); have he : Lattice.lift x=y:= by
    apply Lattice.lift_eq_iff.mpr; refine ⟨?_,fun i=>?_⟩; · funext i; change _ = (((((x i).val :ℤ)) : ZMod (side q n).val)); push_cast; simp
    unfold y; have hz:=h i; omega
 obtain ⟨i,hi⟩:=axis_max x; change pdist x = ( Lattice.lift x i ).natAbs at hi; rw [he] at hi; have hz := h i; unfold y at hi; omega

lemma remote {i:Side}(x:Lattice.Site (periodN i))(h: (periodN i).val ≤8*pdist x)(ht:4*pdist x≤( periodN i ).val)(v:Half): mine (periodN i) (x-thin i v):= by
 unfold mine; by_cases hv:v=0; rw [hv,map_zero,sub_zero]; omega
 let k:= thin i v; have he:pdist k=i.val:= by rw [show pdist k=i.val*pdist v from caress ..,bornlf _ hv,mul_one]
 have hQ:pdist k≤ pdist x+pdist (x-k):= by nth_rw 1 [show k=x+ -(x-k) from (by abel)]; exact ( pdist_triangle _ _ ) |>.trans_eq (by rw [pdist_neg])
 rw [cap_val i] at ht h; change 2*i.val≤16*pdist (x-k); omega

def Θ (q:ℕ+)(n:ℕ):ℝ:= (n:ℝ)*log (q:ℝ)
lemma theta_sc(q:ℕ+)(n:ℕ): exp (-(Θ q n))=epsilon q n:=by rw [exp_neg]; unfold Θ epsilon; rw [Real.exp_nat_mul, exp_log]; positivity
lemma theta_nonneg (q:ℕ+)(n): 0 ≤ Θ q n:= mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg ( by exact_mod_cast (show 1 ≤ q.val from q.property) -- error lt vs ≤
 ))
-- θ^2/log bound PP. super eventual relative q
lemma grows (h:1<q.val): Tendsto (Θ q) atTop atTop:= tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by exact_mod_cast h))
lemma all_ss (h:1<q.val) (r:ℝ) : ∀ᶠ i:ℕ in atTop,r*Θ q i ≤ log ( (dimT (lengthP q) i).val:ℝ ) :=by
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop r)] with i hi; have hp(i:ℕ): (dimT (lengthP q) i).val = 8 * q.val^(i+1)*q.val^(i^2) := congr_arg Subtype.val (recorded q i)
 rw [hp]; push_cast; rw [log_mul (by positivity) (by positivity), log_pow ]; have H:= Real.log_nonneg (show (1:ℝ) ≤ 8*(q:ℝ)^(i+1) from (by
    have he: (1:ℝ) ≤ (q:ℝ)^(i+1) := one_le_pow₀ (by exact_mod_cast h.le); linarith)); apply le_add_of_nonneg_of_le H ?_; unfold Θ; push_cast; have he : 0< log (q:ℝ):= log_pos ( by exact_mod_cast h ); nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi (show 0≤(i:ℝ) from Nat.cast_nonneg _)) he.le]

-- Type depends only on compact physical demand and period schedule. build unconditionally, including empty filters.
structure Locus (q:ℕ+)(K:Set (Points d)) where
 level : ℕ
 x : Grid.offsets q d level
 inK : Grid.sample q level x∈ K
 u : Native q level
 inside : u∈ origins q level

def stopT (q:ℕ+)(K:Set (Points d)): Filter (Locus q K):= Filter.comap Locus.level atTop
lemma files {F:Locus q K → Prop} (h:∀ᶠ i in stopT q K, F i): ∀ᶠ k:ℕ in atTop,∀ i:Locus q K, i.level=k→F i:=by
 rw [stopT,eventually_comap] at h; exact h
variable (q K)
def posterT (μ:ℝ) : Dial.Trial (Locus q K) (Fin d) where
 profile:= { θ i:= Θ q i.level, η i:=μ- Θ q i.level, room i:= theta_nonneg q i.level }
 side i:= lengthP q i.level
 off j i:= Lattice.lift (i.x j)
 head i:= Lattice.lift i.u
local notation "Λ" μ=> posterT q K μ
lemma visit_one(μ:ℝ)(i:Locus q K): dimT ((Λ μ).side) i= LatticePT.side q i.level:= recorded q i.level
lemma billingS (μ:ℝ)(i:Locus q K): Lobby.spacing (Λ μ) i=epsilon q i.level:= theta_sc ..
lemma framesS (μ:ℝ)(i:Locus q K): Dial.testP (Λ μ) i = fun k:Fin d=> MS.Theater.out ((Grid.sample q i.level i.x) k) := by
 funext k; rw [Dial.testP,Tide.lifted, show exp _= _ from billingS q K μ i]; -- i.x. val Hp check
 rfl
end YM.FVAAlt2.Home.Profiles
