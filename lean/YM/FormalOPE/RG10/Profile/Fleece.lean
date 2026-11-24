import YM.FormalOPE.RG10.Profile.Put

/-!
# Integration over one absent marker, in smooth test topology
`loose`: use precisely the tail-of-support compact, hence still in `patch`.
Integration taken at common measurement-length coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Set TopologicalSpace MeasureTheory Filter Topology Metric ContDiffMapSupportedIn
open PertExtension.LatticePT Grid
open scoped Topology ContDiff Distributions Classical BigOperators
variable {n : ℕ} (t : Test (n+1))

def pointOne : Points 1 ≃ₗᵢ[ℝ] E4 where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => E4)).toLinearEquiv
  norm_map' p:= by
     change ‖p 0‖= _; rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),PiLp.norm_sq_eq_of_L2 _ p]; simp
lemma pointOne_eq (p: Points 1) : pointOne p=p 0:=rfl

abbrev leave (n:ℕ): Points (n+1) ≃L[ℝ] E4 × Points n := (Points.peel).toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 _ _ _)
def loose : Compacts (Points n) := ⟨Points.tail '' tsupport t, t.hasCompactSupport.image (by exact continuous_snd.comp (leave n).continuous)⟩
lemma safe : (loose t:Set (Points n)) ⊆ patch n := by
 rintro x ⟨y,hy,rfl⟩ i j he; exact Fin.succ_inj.mp ((t.tsupport_subset hy : Injective (WithLp.ofLp y)) (show y i.succ=y j.succ from he))

def wool (y:Points 1) : ContDiffMapSupportedIn (Points n) ℂ ⊤ (loose t) :=
 .of_support_subset (f:=fun x:Points n=> t (Points.cons (y 0) x))
    (t.contDiff.comp (f:=fun x=> (leave n).symm (y 0,x)) ((leave n).symm.contDiff.comp (by fun_prop)))
    (fun x hx=> ⟨_,subset_closure (show Points.cons (y 0) x ∈ support t from hx),rfl⟩)
lemma spring : Continuous (wool t):= by
 apply volumeContinuous
 exact t.contDiff.comp (f:=fun p:Points 1 × Points n=> (leave n).symm (pointOne p.1,p.2)) ((leave n).symm.contDiff.comp ((pointOne.toContinuousLinearEquiv.contDiff.comp contDiff_fst).prodMk contDiff_snd))
lemma trim : HasCompactSupport (wool t):=by
 let c := pointOne.symm ∘ (Points.head (n:=n))
 refine HasCompactSupport.intro (t.hasCompactSupport.image (show Continuous c from pointOne.symm.continuous.comp (continuous_fst.comp (leave n).continuous))) (fun x hx=>?_ )
 ext1 y; change t (Points.cons _ _) = 0
 apply image_eq_zero_of_notMem_tsupport; exact fun h=>hx ⟨(Points.cons (x 0) y),h,(pointOne.symm_apply_apply x)⟩

def fleece : ContDiffMapSupportedIn (Points n) ℂ ⊤ (loose t) := (put _ (spring t) (trim t) (q:=3) (by decide)).choose
lemma total (x:Points n) : fleece t x= ∫ y:Points 1, t (Points.cons (y 0) x):= (put _ (spring t) (trim t) (q:=3) (by decide)).choose_spec.2 x
lemma dried {q:ℕ+} (hq:1<q.val) : Tendsto (purse (q:=q) (wool t)) atTop (𝓝 (fleece t)) := by
 obtain ⟨u,hu,h⟩:= put _ (spring t) (trim t) hq
 exact (ContDiffMapSupportedIn.ext (fun x=>(h x).trans (total t x).symm)) ▸ hu

def marginal : Test n:= TestFunction.ofSupportedIn (safe t) (fleece t)
def takings (q:ℕ+) (m:ℕ) : Test n:= TestFunction.ofSupportedIn (safe t) (purse (q:=q) (wool t) m)
lemma takings_at (q:ℕ+)(m:ℕ)(x:Points n): takings t q m x = epsilon q m ^ 4 • ∑ i:offsets q 1 m, t (Points.cons (point q m (i 0)) x) := by
 change (purse (q:=q) _ m) _=_; simp only [purse, mul_one,smul_apply,sum_apply]; rfl
lemma marginal_total (x:Points n): marginal t x=∫ y:E4,t (Points.cons y x):=
    (total t x).trans (pointOne.measurePreserving.integral_comp pointOne.toHomeomorph.measurableEmbedding (g:=fun y=> t (Points.cons y x)))
end YM.FormalOPE.RG10.Profile
