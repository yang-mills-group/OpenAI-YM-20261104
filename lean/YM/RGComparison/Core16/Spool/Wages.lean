import YM.RGComparison.Core16.Spool.Beacon
/-!
# Stencil population estimation; synthesis from actual C.Family. Non-normalized operators
at dyadic* analysis, accounting arcs at incoming coupling g. Use ext Tick θ physical `Move` not
constructed only at launch bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Spool
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Lumen Lumen.Planet Parcel Parcel.Oven Next.Fluctuations Finset Complex Asymptotics
open Lumen.Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {ι : Type}[Fintype ι] (J:ι→ Lamp G)

private lemma blast {f : (ι→G.Color)→ℂ}(hf : ContDiffAt ℝ ω f 0) (h0:f 0=0): RadialOrder 1 f:=by
    intro x; let H:=fun t:ℝ=>f (t • x); have ht : ContDiffAt ℝ ω H 0:= (((show (0:ℝ) • x=0 from zero_smul ..) ▸ hf)).comp (f:=fun t:ℝ=>t • x) _ (by fun_prop)
    obtain ⟨C,hC,h⟩:= (ht.differentiableAt (by simp)).hasFDerivAt.isBigO_sub.exists_pos
    refine ⟨C,hC.le,?_⟩; filter_upwards [h.bound.filter_mono (show Tested.germ≤𝓝 (0:ℝ) from nhdsWithin_le_nhds),Tested.eventually_pos] with t ht hq; simpa only [H,zero_smul,h0,sub_zero,Real.norm_of_nonneg hq.le,pow_one] using ht
private lemma travel_heat {Y:(ι→G.Color)→CoverConfig G}(hv:∀ i, ContDiffAt ℝ ω (fun x=>G.mat (Y x i)) 0)(v:Cover)(l:Walk):ContDiffAt ℝ ω (fun x=> G.mat (travel (Y x) v l)) 0 := by
    induction l generalizing v with
    | nil=> simp_rw [travel]; exact contDiffAt_const
    | cons d l h=> simp_rw [travel,G.mat_mul]; apply ContDiffAt.mul _ (h _); unfold Step.read; split
                   · simp_rw [G.mat_inv]; exact ((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp (f:=fun x=> G.mat (Y x _)) _ (hv _))
                   exact hv _
private lemma stream_one (v:Cover)(l:Walk): travel (1:CoverConfig G) v l = 1:=by induction l generalizing v with
    | nil=> rfl
    | cons d l h=>rw [travel,h]; simp [Step.read]

section slot
variable {Y : (ι→G.Color) → CoverConfig G}(hm: ∀ i, ContDiffAt ℝ ω (fun x=>G.mat (Y x i)) 0)
    (he:Y 0=1) {k:ℕ}(T : Fin k → RG.Slot)

def drip (Y : (ι→G.Color)→ CoverConfig G)(s:RG.Slot)(e:G.ColorIndex)(x:ι→G.Color):ℂ:= Complex.ofReal (s.eval (Y x) e)
include hm in
lemma single_hot (a:RG.Slot)(e:G.ColorIndex): ContDiffAt ℝ ω (drip Y a e) 0:=by
    change ContDiffAt ℝ ω (Complex.ofRealCLM ∘ (EuclideanSpace.proj e ∘ (fun x=> a.eval (Y x)))) 0
    refine Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((EuclideanSpace.proj e : G.Color→L[ℝ] ℝ).contDiff.contDiffAt.comp (f:=fun x=> a.eval (Y x)) _ ?_)
    simp_rw [Slot.eval, ← G.curvature_conjugate]; apply curvature_diff_mat; simp only [G.mat_mul,G.mat_inv]
    exact (((travel_heat hm ..).mul (travel_heat hm ..)).mul ((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (travel_heat hm ..)))
include he in
omit [Fintype ι] in
lemma single_zero (a:RG.Slot)(e:G.ColorIndex): drip Y a e 0=0:=by simp_rw [drip,he,Slot.eval,faceValue,stream_one]; simp
include hm
lemma signature (p : Bid.Pose G k):ContDiffAt ℝ ω (fun x=>Bid.lumin p (Bid.mapped T (Y x))) 0:= by
    let A:=Fin k × G.ColorIndex
    let f (x:ι→G.Color)(i:A):= drip Y (T i.1) i.2 x
    let t (i:A) := fun x=> f x i
    change ContDiffAt ℝ ω (fun x=> MvPolynomial.aeval (f x) p) 0
    induction p using MvPolynomial.induction_on with
    | C a=> simp_rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]; exact contDiffAt_const
    | add p q h ih=> apply (h.add ih).congr_of_eventuallyEq (f₁:=fun x=>_) (Eventually.of_forall fun i=> map_add ..)
    | mul_X p i h=> simp_rw [map_mul,MvPolynomial.aeval_X]; exact h.mul (single_hot hm ..)
include he
lemma shadow (w:ℕ)(p:Bid.Pose G k)(hz : Bid.lows p w) (u:ι→G.Color): Bill w (fun t:ℝ=> Bid.lumin p (Bid.mapped T (Y (t • u)))):=by
    let h (i:Fin k × G.ColorIndex)(t:ℝ):= drip Y (T i.1) i.2 (t • u)
    -- convert to finite sum Bill
    convert! bill_sum p.support (fun v=> (fun t:ℝ=> MvPolynomial.coeff v p * ((∏ j∈ v.support, h j ^ v j) t))) ?_ using 1
    · ext t; unfold Bid.lumin; rw [MvPolynomial.aeval_def,MvPolynomial.eval₂_eq]; simp only [Finset.sum_apply, Finset.prod_apply,Pi.pow_apply]; rfl
    intro i hi; apply bill_ge (bill_mul (bill_const _) (bill_product i.support i _ (fun j _=> (show Bill (i j) (_) from ?_)))) (by simpa only [Nat.zero_add,Finsupp.sum] using hz i hi)
    have hh: Bill 1 (h j):= blast (single_hot hm ..) (single_zero he ..) u; simpa only [mul_one] using! bill_pow hh (i j)
end slot

def heavens (i:ι) (v:Slice J→G.Color): CoverConfig G:= wind (J i) fun l=> launch (v ⟨i,l⟩)
lemma pastor (i:ι) (e:Edge Cover): ContDiffAt ℝ ω (fun x=> G.mat (heavens J i x e)) 0:=by
    unfold heavens wind; split; rename_i h
    · let p : Slice J:=⟨i,(⟨e.1,h⟩, e.2)⟩; change ContDiffAt ℝ ω ((fun x=> G.mat (launch x)) ∘ (fun (v:Slice J→ G.Color) => v p)) 0; exact (launch_data (G:=G)).comp (f:=fun v:Slice J→ G.Color=> v p) _ (contDiff_apply ℝ _ p).contDiffAt
    exact contDiffAt_const
omit [Fintype ι] in
lemma past_zero (i:ι):heavens J i 0=1:=by funext x; unfold heavens wind; split; exact launch_zero; rfl
lemma storm (i:ι) : ContDiffAt ℝ ω ((J i).action ∘ heavens J i) 0:=by
    obtain ⟨k,B,T,h,-⟩:= (J i).basis; rw [h]; exact signature (pastor J i) B T
lemma sphere (i:Bool): ContDiffAt ℝ ω (look i ∘ sight J) 0:= by
    exact (look i).contDiff.contDiffAt.comp (f:=sight J) _ (contDiffAt_prod fun i _=> storm J i)
lemma painted (i:Bool): Lumen.Zeros (power J) (look i ∘ sight J):=by
    have hx: RadialOrder (power J) (fun x=> look i (sight J x)):=by
        intro x
        let f (t:ℝ):= sight J (t • x); let g (a:ι)(t:ℝ):= (J a).action (heavens J a (t • x)); have he : f= ∏ j,g j:=by ext; simp_rw [Finset.prod_apply]; rfl
        have hp (a:ι): Bill ((J a).order) (g a):=by
            obtain ⟨k,B,T,h,hT⟩:= (J a).basis; unfold g; rw [h]; exact shadow (pastor J a) (past_zero J a) B _ T hT x
        obtain ⟨C,hC,h⟩:= (show Bill (power J) f from (he ▸ (bill_product _ _ _ (fun i _=> hp i))))
        refine ⟨‖look i‖*C,by positivity,h.mono (fun x hx=> ((look i).le_opNorm (f x)).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_assoc ..).symm))⟩
    exact fun _ he=> jets_vanish (f:=look i ∘ sight J) ((sphere J i).of_le le_top) hx he
end YM.RGComparison.Core16.Spool
