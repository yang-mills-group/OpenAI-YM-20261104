import YM.X.Gravity.Sweep
import YM.X.Gravity.Zoom
/-!
# Orientation resolution by shell test detectors (unphysical; not grams) and unscaled price.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "e"=>epsilon q
variable (P:Word G)(φ:Floor R)
def exposed (q:ℕ+)(P: Word G)(φ:Floor R):= fun i=> bloom P.d (warp q P φ i)
def oracle (n:ℕ): Module.End ℂ (Book G):= (((weightedHomogeneousComponent (vapor G) n)).comp (LinearMap.id-watch G n))
lemma rise₀ (p:Book G) : oracle n p= leaf (vapor G) n (p-watch G n p):=rfl
lemma rise_mem (p:Book G)(d:ℕ): oracle d p∈saddleX G d:= by
   rw [rise₀]; refine ⟨weightedHomogeneousComponent_mem ..,(LinearMap.mem_ker).mpr ?_⟩
   rw [← leaf_watch,map_sub, watch_twice,sub_self]; unfold leaf; rw [map_zero]
abbrev spoon (G:Gauge):= (Sigma (Okay G)) × (Long G)
def tasteX (p: spoon G):Book G→ₗ[ℂ]ℂ:= (probeL p.2).toLinearMap.comp (testP p.1.2).toLinearMap
lemma tasting (p:Book G)(d:ℕ)(T:p∈saddleX G d)(h:∀ x,tasteX x p=0):p=0:= by
    have hv: ∀ n, ∀ A:Okay G n,testP A p=0:= fun n A=> probe_ext fun x=> by rw [map_zero]; exact h (⟨n,A⟩,x)
    exact (fixed_for p hv).symm.trans (LinearMap.mem_ker.mp (show p∈LinearMap.ker (watch G d) from T.2))
lemma exposure (i:ℕ)(h:n≤P.d): leaf (vapor G) n (exposed q P φ i)=leaf (vapor G) n (trumpet (Okay G) valP P.d (warp q P φ i)):= leaf_level _ _ n h
lemma sight (i:ℕ)(he:n≤P.d)(A:Okay G k): testP A (oracle n (exposed q P φ i))=testP A (leaf (vapor G) n (trumpet (Okay G) valP P.d (warp q P φ i))):= by rw [rise₀,show leaf (vapor G) n (exposed q P φ i - watch G n _)=(leaf (vapor G) n (exposed q P φ i)) - (leaf (vapor G) n (watch G n (exposed q P φ i))) from map_sub _ _ _, leaf_watch, exposure _ _ i he,map_sub,show testP A (watch G n _) = 0 from testP_local A _, sub_zero]
lemma or_real (a:ℝ)(p:spoon G)(x:Book G): tasteX p (a • x)=a • tasteX p x:= map_smul ((tasteX p).restrictScalars ℝ) a x
include hq
lemma sep_peer (h:n≤P.d)(x:spoon G): Released (fun i=> tasteX x ( (e i ^(n-P.d:ℤ)) • oracle n (exposed q P φ i))):= by
    rcases x with ⟨⟨k,T⟩,x⟩; simp_rw [or_real]; change Released (fun i=> _ • probeL x (testP T (oracle n (exposed q P φ i)))); simp_rw [sight P φ _ h T]; rcases le_or_gt n k with ht|hf
    · have he (p:Book G): testP T (leaf (vapor G) n p) =0:= post_zero T _ (weightedHomogeneousComponent_mem ..) ht
      simp_rw [he,map_zero,smul_zero]; exact Released.zero
    let u:= n-(k+1)
    have hu:n=u+(k+1):=by omega
    have hx' : k<P.d:=hf.trans_le h
    conv => enter [1,i]; rw [hu,← post_leaf T,step_record T hx'] -- syntax
    convert (curved (q:=q) (m:=u) hq T φ P x (by omega)) using 1; rw [Nat.add_comm (k+1) u]; rfl
lemma or_clamp (h:n≤P.d): (fun i=> (e i ^(n-P.d:ℤ)) • oracle n (exposed q P φ i))∈Badge (Book G) Released (saddleX G n):= by
   apply plenty (P:=crew) tasteX (saddleX G n) (fun p=> tasting p n); · intro i; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact Submodule.smul_mem _ _ (rise_mem ..)
   exact sep_peer hq P φ h
lemma separator_lead (h:n≤P.d): (fun i=>e i • leaf (vapor G) n (exposed q P φ i)) ∈ Badge (Book G) (fun p=>p∈fades ℂ) (partX G n):= by
   apply plenty (P:=fades ℂ) (fun x:Long G=> (probeL x).toLinearMap) _
   · intro x c h; exact probe_ext fun u=> (h u).trans (map_zero (probeL u)).symm
   · intro i; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact Submodule.smul_mem _ _ (weightedHomogeneousComponent_mem ..)
   intro x; let b:=probeL x; let c:=fun i=>leaf (vapor G) n (exposed q P φ i); let f(i:ℕ):= b (e i • c i); change Tendsto f L (𝓝 0); refine (pure_root (q:=q) (k:=n) hq φ P (x:=fun i=>x) (fun i=> ⟨x i,tendsto_const_nhds⟩) h).congr (fun i=> ?_); unfold f c; rw [show ∀ (x:Book G), b (e i • x)= e i • b x from fun x=> map_smul (b.toLinearMap.restrictScalars ℝ) .., exposure P φ _ h]; rfl
end YM.PositionX.Gravity
