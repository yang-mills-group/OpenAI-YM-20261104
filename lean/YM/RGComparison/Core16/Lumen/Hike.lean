import YM.RGComparison.Core16.Lumen.Rays
/-!
# Marker word-test Schwinger step derivative billing (unit orientations already paid)

Hold masks and positions fixed at event. V=exp(g*u) in real construction, all data on this one
coupled call later. No Cylinder.NormCap invoked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Gravity
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T) (i j:Wire G ι)

-- curved coordinate angular shift
def paper (x:Sky G ι):ℝ:=if i.1=j.1 then (roll i.2 (G.mat (x i.1))) j.2 else 0
omit [Fintype ι] in
lemma rotated (g:ℝ)(x:Sky G ι): HasDerivAt (fun t=> tally g j (raybay i t x)) (paper i j x / g) 0:= by
    by_cases h:i.1=j.1
    · rw [paper,if_pos h]; unfold tally curve raybay gust; simp only [h,↓reduceIte]; have hd := (EuclideanSpace.proj j.2:G.Color→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 (sleeve i.2 (x j.1))
      exact hd.div_const _
    simp_rw [tally,curve,raybay,gust,paper,if_neg h,if_neg (Ne.symm h),_root_.zero_div]; exact hasDerivAt_const ..
omit [Fintype ι] in
lemma paper_cont:Continuous (paper i j):=by unfold paper; split; exact (EuclideanSpace.proj j.2:G.Color→L[ℝ] ℝ).continuous.comp ((roll_hot i.2).continuous.comp (G.continuous_mat.comp (continuous_apply i.1))); exact continuous_const

def depart (g:ℝ)(w:Rail G ι): Sky G ι→ℝ:= match w with
 | []=>0
 | a::w=> paper i a * sing w g + tally g a * depart g w  -- implicit i?

omit [Fintype ι] in
lemma currents (g:ℝ)(x:Sky G ι)(w:Rail G ι): HasDerivAt (fun t=> sing w g (raybay i t x)) (depart i g w x/g) 0:= by
    have hP:raybay i 0 x=x:= gust_zero ..
    induction w with
    | nil=> simp_rw [sing_nil,depart]; simp only [Pi.zero_apply,_root_.zero_div]; exact hasDerivAt_const ..
    | cons j w h=> simp_rw [sing_cons]; apply ((rotated i j g x).fun_mul h).congr_deriv; rw [depart,Pi.add_apply,Pi.mul_apply,Pi.mul_apply,hP]; ring
omit [Fintype ι] in
lemma depart_cont (g:ℝ) (w:Rail G ι): Continuous (depart i g w):=by
    induction w with
    | nil=> rw [depart]; exact continuous_const
    | cons j w h=> rw [depart]; exact ((paper_cont ..).mul (sing_cont ..)).add ((tally_cont ..).mul h)

variable (b:ContDiffBump (0:ℝ))
def guide : Stuff G ι Unit:=fun _=> .inl i.1

def wing (G:Gauge)(q: Option (G.ColorIndex × G.ColorIndex))(x:Unit→ G.Color):ℝ:=match q with
    | some (i,j)=> (roll i (G.mat (launch (x ())))) j
    | none=>0

def scorecard := if i.1=j.1 then some (i.2,j.2) else none

def belt : Melody G ι:=fun _=>P.dark b i * paper i j
def fove : Melody G ι:=fun g=> g • P.faint b i
lemma wing_smooth (j:Option (G.ColorIndex × G.ColorIndex)):ContDiffAt ℝ ∞ (wing G j) 0:= by
    rcases j with _|⟨u,v⟩
    · exact contDiffAt_const
    apply ContDiffAt.of_le ?_ le_top
    exact (EuclideanSpace.proj v : G.Color→L[ℝ] ℝ).contDiff.contDiffAt.comp (𝕜:=ℝ) _ ((roll_hot u).contDiffAt.comp (𝕜:=ℝ) (0:Unit→G.Color) ((@launch_data G).comp (f:=fun (x:Unit→G.Color)=>x ()) (0:Unit→ G.Color) (contDiff_apply ℝ _ _).contDiffAt))

variable {b}(hb:Dust b X.δ)

private lemma envelope_bump (b:ContDiffBump (0:ℝ))(G:Gauge): ∃ C:ℝ,0≤C ∧ ∀ i:G.ColorIndex, ∀ x:G.El, |shaft b i x|+‖roll i (G.mat x)‖≤C:=by
    let f (i:G.ColorIndex): G.El→ℝ:=fun x=>|shaft b i x|+‖roll i (G.mat x)‖
    have h i: Envelope (f i):=havenreal ((shaft_cont b i).abs.add ((roll_hot i).continuous.comp G.continuous_mat).norm)
    choose c hc using fun i=> (h i).cost; refine ⟨∑ i, |c i|,sum_nonneg (fun _ _=>abs_nonneg _),fun i x=>?_⟩
    refine ((le_abs_self (f i x)).trans (hc i x)).trans ((le_abs_self _).trans ?_); exact single_le_sum (fun i _=> abs_nonneg (c i)) (mem_univ _)
include hb
lemma sky (Y:Good X):∃ C:ℝ,0≤C ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(n:Side)(P:Planet X n ι k T),P.Steady→ ∀ (i:Wire G ι), Visible X (wing G none) (fove P i b) (guide i) (patchN X.sector) C ∧ ∀ j,
     Visible X (wing G (scorecard i j)) (belt P i j b) (guide i) (patchN X.sector) C:=by
    obtain ⟨C,hC,h⟩:= envelope_bump b G; have ht:=Y.thick
    have hp:0≤X.knot*C:=mul_nonneg ht.2.1.le hC; refine ⟨C+X.knot*C,add_nonneg hC hp,fun ι k T _ _ _ n P H i=>?_⟩
    let q:=P.heat i.1; have hh:= shelter H (k':=i); have he:celery (guide i) q X.Q:=fun _=> P.loc_heat i.1
    constructor
    · refine ⟨fun g _=> (Envelope.const _).mul (P.whirl b i).2,fun g hg x=>?_,q,hh,he,fun g hg he x hx=>?_⟩
      · unfold fove; rw [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hg.1]; apply le_trans (b:= X.knot * C) ?_ (le_add_of_nonneg_left hC)
        apply mul_le_mul hg.2 _ (abs_nonneg _) ht.2.1.le; unfold faint; split; exact (le_add_of_nonneg_right (norm_nonneg _)).trans (h ..); rwa [abs_zero]
      unfold fove; rw [Pi.smul_apply,(live i hb hx).2,smul_zero]; rfl
    intro j; refine ⟨fun g _=> (P.whirl b i).1.mul (havenreal (paper_cont ..)),fun g hg x=>?_,q,hh,he,fun g hg he x hx=>?_⟩
    · rw [belt,Pi.mul_apply,abs_mul, abs_of_nonneg (P.dark_grip b i x|>.1)]; refine (mul_le_of_le_one_left (abs_nonneg _) (P.dark_grip b i x|>.2)).trans (le_trans (b:=C) ?_ (le_add_of_nonneg_right hp)); unfold paper; split
      · exact (mono_cone _ _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (h ..))
      rwa [abs_zero]
    rw [belt,Pi.mul_apply,(live i hb hx).1,one_mul]; unfold scorecard paper; split
    · have ht:G.chord (x i.1)< X.δ:= (hx i.1 (P.loc_heat i.1)).trans (by linarith [hb.pos]); unfold wing; rw [show (g • book (guide i) g x) ()= G.curvature (x i.1) from smul_inv_smul₀ he.ne' _, Y.reenter _ ht]
    rfl
end YM.RGComparison.Core16.Lumen.Gravity
