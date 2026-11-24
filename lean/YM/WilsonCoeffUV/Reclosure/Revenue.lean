import YM.WilsonCoeffUV.Reclosure.Ordered
import YM.Next.STATIONARY.Shape.ClassicalMatch
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Payments
/-!
# Unmasked path to its lit constituents and prices
Also exposes termwise normalized jets in all finite Periods -- these
are auxiliary periodized **kernels**, not finite-volume unnormalized density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open AnalyticNext.QuarticMatch.Estimate
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s a:ℝ}
variable (A:Atom G t)

namespace Near
abbrev Grid (A:Atom G t):= {x : Cover // x∈A.stencil} × Hooks G
def closeU (w:Lawn (Grid A)): CoverConfig G:= fun i=> G.lieExp (coatC G fun j=> if h:i.1∈ A.stencil then w (⟨i.1,h⟩,coord i.2,j) else 0)
def line (w:Lawn (Grid A)) : ℝ := A.poly fun j => (A.leg j).eval (closeU A w)
def lead : Leads Cover (Hooks G) (Grid A):= fun i=> some (i.1.1,i.2)

def slab (x:Site c): Matrix (Grid A) (Woods G c) ℝ:= casement (lead A) x
lemma slabrow (x:Site c)(i:Grid A) : slab A x i=Pi.single (x+wrap c i.1.val,i.2) 1:= plank_origin _ x i (j:=foldUnder c (i.1.1,i.2)) rfl
lemma slap (x:Site c) (i:Grid A)(w:Lawn (Woods G c)):(slab A x *ᵥ w) i=w (x+wrap c i.1.val,i.2):= by rw [mulVec,slabrow,single_one_dotProduct]

def meter (x:Site c)(a:Link G c):ℝ := A.unmasked (input G c a) x
lemma meter_p (x:Site c):meter A x=fun w=> line A (slab A x*ᵥ w):= by
    funext w; unfold meter Atom.unmasked RG.Slot.atSite line; apply congr_arg A.poly; funext i; apply (A.leg i).covered; intro j h e
    have he : j.1 ∈ A.stencil := Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,h⟩)
    change (represent _ _ = _); rw [Work.F03.represent_link]; unfold closeU; apply congr_arg; ext v; change w (wrap c j.1+x,coord j.2,v)=_
    change w _=(if h:j.1∈A.stencil then (slab A x*ᵥ w) (⟨j.1,h⟩,coord j.2,v) else 0); rw [dif_pos he, slap, add_comm x]

lemma tickets : ∀ᶠ n:Side in atTop, Injective (fun i:Grid A=> foldUnder n (i.1.1,i.2)) := by
    have HH (i:Grid A):∀ᶠ n in atTop,∀ j:Grid A,foldUnder n (i.1.1,i.2)=foldUnder n (j.1.1,j.2)→i=j := eventually_all.mpr fun j=> (fold_faith (i.1.1,i.2) (j.1.1,j.2)).mono fun _ z h=> by simpa only [Prod.mk.injEq,Subtype.val_inj,← Prod.ext_iff] using z.mp h
    exact (eventually_all.mpr HH).mono (fun n hn=> fun i=> hn i)
lemma meter_hot (x:Site c): ContDiff ℝ ω (meter A x):= (Cargo.effective A x).comp (arm G c 1).contDiff
lemma shines : Green (line A):= by
   obtain ⟨n,h⟩:= (tickets A).exists
   let f (i:Grid A):= foldUnder n (i.1.1,i.2)
   let L:=(slab A (0:Site n))
   have hx i : L i= Pi.single (f i) 1:=by unfold L f foldUnder; rw [slabrow]; simp
   have he (w:Lawn (Grid A)): L *ᵥ (L.transpose*ᵥ w)=w:=by
       ext j; rw [mulVec, hx, single_one_dotProduct,mulVec,dotProduct]; simp_rw [transpose_apply,hx]; rw [Finset.sum_eq_single j]; simp
       · intro y _ hy; rw [Pi.single_eq_of_ne (fun hi=>hy ((h hi).symm)), zero_mul]
       simp
   rw [show line A=(meter A (0:Site n)) ∘ (LinearMap.toContinuousLinearMap (Matrix.mulVecLin L.transpose)) from ?_]; exact ((meter_hot ..).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin L.transpose)).contDiff).contDiffAt
   ext w; rw [Function.comp_apply,meter_p]; change _=line A (L *ᵥ (L.transpose*ᵥ w)); rw [he]

lemma frames (x:Site c) (k): rye (meter A x) k= fade (slab A x) (shine (rye (line A) k)) k:=by
   have he:= congr_fun (beam (slab A x) (line A) (shines A) k) k
   rw [← meter_p] at he; simp_rw [sprig,Nat.add_zero] at he; rw [shine_lit] at he; exact he

lemma slab_size (x: Site c)(i:Grid A)(v: Woods G c)(h:slab A x i v≠0): (tor c).gap x v.1 ≤ A.length:= by
    rw [slabrow,Pi.single_apply] at h; split at h; swap; · simp at h
    rename_i he; subst v; change size (lift (x+wrap c (i.1.val)- x)) ≤ A.length; rw [add_sub_cancel_left]; apply (wrap_size ..).trans; have he:= i.1.property
    change i.1.val ∈ insert (0:Cover) (Finset.univ.biUnion fun z=>(A.leg z).stencil) at he; rw [Finset.mem_insert, Finset.mem_biUnion] at he; rcases he with a|⟨v,hw,hv⟩
    · rw [a]; simp [Laurent.size]
    exact (slot_weight _ hv).trans (Finset.single_le_sum (f:=fun i=>(A.leg i).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ v))
lemma belonging (x:Site c)(i:Fin k→Woods G c)(h: rye (meter A x) k i≠0)(j:Fin k): (tor c).gap x (i j).1 ≤ A.length:= by
   by_contra H; apply h; rw [frames]; unfold Blue.fade; apply Finset.sum_eq_zero; intro s _; have he:slab A x (s j) (i j)=0:=by by_contra w; exact H (slab_size A _ _ _ w)
   rw [Finset.prod_eq_zero (Finset.mem_univ j) he,zero_smul]
-- evaluate cost per parameter exactly. arm converts sup norm.
lemma supplied (i:Woods G c) : ‖arm G c 1 (Pi.single i 1)‖ ≤ 1 := by
   apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro x; by_cases h:(i.1,i.2.1)=x
   · subst x
     have he : arm G c 1 (Pi.single i 1) (i.1,i.2.1)= EuclideanSpace.basisFun G.ColorIndex ℝ i.2.2:= by
        ext x; rw [arm_apply]; by_cases H:x=i.2.2; subst x; simp
        have ht:(i.1,i.2.1,x)≠i:=by intro p; exact H (congr_arg (fun k:Co c (Hooks G)=>k.2.2) p)
        simp [ht,H]
     rw [he]; simp
   rw [show arm G c 1 (Pi.single i 1) x=0 from ?_]; simp
   ext j; change Pi.single (M:=fun _:Woods G c=>ℝ) i 1 (x.1,x.2,j)=0; rw [Pi.single_eq_of_ne]; intro e; apply h; rw [← e]

def flour (G:Gauge)(s:ℝ)(t k:ℕ):ℝ:= (k.factorial:ℝ)⁻¹*((2:ℝ)^k*gratuity G (down s k) k)^t
lemma flour_nn (G:Gauge)(s:ℝ)(t k:ℕ):0≤ flour G s t k:=by unfold flour; have h:= gratuity_pos G (down s k) k; positivity
lemma flourished (o:Site c)(hp:0<s)(x: Fin k→Woods G c) : ‖rye (meter A o) k x‖≤ A.budget s * flour G s t k:=by
    let P:Lawn (Woods G c) →L[ℝ] fieldDir G c 1:= (arm G c 1).toContinuousLinearMap
    have hu: meter A o=(Cargo.effect A o) ∘ P:=rfl
    let z (j: Fin k):= Pi.single (M:=fun _:Woods G c=>ℝ) (x j) 1
    let H:= iteratedFDeriv ℝ k (Cargo.effect A o) 0
    have he: AnalyticAt ℝ (Cargo.effect A o) (P 0):= ((Cargo.effective ..).contDiffAt).analyticAt
    rw [fiscal_vol, Tensor.coeff, _root_.smul_apply,hu,wired P he,map_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
     _ ≤ ((k.factorial:ℝ)⁻¹)* (‖H‖ * ∏ j, ‖(P ∘ z) j‖):=mul_le_mul_of_nonneg_left (H.le_opNorm _) (by positivity)
     _ ≤ ((k.factorial:ℝ)⁻¹)* ‖H‖:= mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) ((Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>supplied (x j))).trans_eq (Finset.prod_const_one))) (by positivity)
     _ ≤ _:= (mul_le_mul_of_nonneg_left (neighbors 0 (by rw [norm_zero]; positivity) hp A k le_rfl o) (show 0 ≤ ((k.factorial:ℝ)⁻¹) by positivity)).trans_eq (by unfold flour; ring)

-- true and period kernels. Iris cut

def archInk (n:Side)(k:ℕ) : Ten ℝ (Woods G n) k := ∑ z:Site n,rye (meter A z) k
def coverInk (k:ℕ) : Ten ℝ (YForest G) k:= sunflower (lead A) (shine (rye (line A) k)) k
lemma orchid (k:ℕ): Yields (fun n=>archInk A n k) (coverInk A k):= (sunflowerY ..).congr (Eventually.of_forall fun n=>by simp only [iris_apply, archInk, frames]; rfl)
lemma cousins (c:Side)(x: Fin k→Woods G c) (p:Site c)(hv:∀ i,(tor c).gap p (x i).1 ≤ A.length): soar (tor c) x≤ A.length+A.length:=league_le (tor c) (Prod.fst ∘ x) fun i j=> ((tor c).tri _ p _).trans (add_le_add (by rw [(tor c).swap _ p]; exact hv i) (hv j))
def steep (s:ℝ):= s/4

def garden (G:Gauge)(s:ℝ)(t k:ℕ):= flour G (steep s) t k*sheetPay (steep s)
lemma garden_nn (G:Gauge) (h:0<s)(t k:ℕ):0≤ garden G s t k:= mul_nonneg (flour_nn ..) (sheetPay_pos _ (by unfold steep; linarith)).le
lemma garage (p:Site c)(X:stars G k c)(h:0<s): ‖rye (meter A p) (k+1) X‖ ≤ (A.budget s*flour G (steep s) t (k+1))*Real.exp (-(steep s)*soar (tor c) X)*Real.exp (-(steep s)*(tor c).gap (X 0).1 p):=by
    let K:=flour G (steep s) t (k+1)
    let L:=A.magnitude
    let v:= steep s
    have hp:0<v:=div_pos h (by norm_num)
    have hl:0 ≤ L:= Finset.sum_nonneg fun i _=> abs_nonneg _
    have H:0≤K:=flour_nn ..
    change ‖_‖≤ (L*Real.exp (s*A.length)*K)* Real.exp (-v*(soar (tor c) X)) * _
    by_cases he:rye (meter A p) (k+1) X=0; · rw [he,norm_zero]; positivity
    apply (flourished A p hp X).trans
    let d:=soar (tor c) X
    let f:=(tor c).gap p (X 0).1
    have hh : (d:ℝ) ≤ A.length + (A.length:ℝ):= by exact_mod_cast cousins A c X p (fun i=> belonging A p X he i)
    have hf : (f:ℝ)≤ A.length:= by exact_mod_cast belonging A p X he 0
    rw [(tor c).swap _ p];
    calc
     _ = L*K*Real.exp (v*A.length):=mul_right_comm L _ K
     _ ≤ L*K*Real.exp ((s*A.length+ -v*d)+ -v*f):=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by unfold v steep; nlinarith)) (by positivity)
     _ = _:= by rw [Real.exp_add, Real.exp_add]; unfold d f v; ring
lemma artical (h:0<s)(n:Side) (k:ℕ) : Amber (tor n) (steep s) (A.budget s*garden G s t (k+1)) (archInk A n (k+1)):=by
    have hl:0 ≤ A.budget s:=by unfold Atom.budget Atom.magnitude; positivity
    refine ⟨mul_nonneg hl (garden_nn G h t _),fun x=>?_⟩
    rw [archInk,Finset.sum_apply]; apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (fun i _=> garage A i x h)).trans
    rw [←Finset.mul_sum]; have he := taxi_volume (x 0).1 (steep s) (div_pos h (by norm_num)); have ht := flour_nn G (steep s) t (k+1)
    exact (mul_le_mul_of_nonneg_left he (show 0 ≤ A.budget s*flour G (steep s) t (k+1)* Real.exp (_) from by positivity)).trans_eq (by unfold garden; ring)
lemma rocksA (h:0<s)(k): Amber terrain (steep s) (A.budget s*garden G s t (k+1)) (coverInk A (k+1)):=by
    have hl:= artical A h
    refine ⟨(hl 1 k).1,fun x=>le_of_tendsto ((orchid A (k+1)).point x).norm ?_⟩
    filter_upwards [touched x] with n hn; rw [← hn]; exact (hl n k).2 _
end Near
end YM.WilsonCoeffUV.Bank.Mosaic
