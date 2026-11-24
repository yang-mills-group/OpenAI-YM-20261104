import YM.FormalOPE.RG10.Position.Search
import YM.Pert.Triangle.End
/-! # Shared $\mathtt{b,U,U}$ test for *dressed* (in \bbR[[g_N]])

Pin use of the accepted `Triangle` detector/template, NOT reusing `YM.Pert` gauge or scale
frames. All rotations already integrated in this fixed real template of separated supports.
Includes the multiplicative stencil/test conventions above, particularly joint averages over
origins in each moment and density factor. Take the test on the **connected function of the
resulting formal array**, not the response in a single origin. On each moment this is exactly
implemented by product profiles (`Peal` here gives all marginals, no multiplying by the integral
of forgotten tests). Normalize including the disconnected vacuum subtraction even on the
regulator. Identify the positive knot constant with the first-order WilsonX continuum diagnostic
only on supplying that RG11 input; not derived from this test substrate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position.Peal
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric Pert.Triangle PertExtension.Position PertExtension.Physical
  PowerSeries Triangle
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} (F : Frames G) {q m : ℕ}
local notation "Θ" => Fin 3
local notation "R" => conventionRadius
-- convenient disjoint radial collars
def radii : Θ→ℝ := ![R,12,0]
theorem ordered (i:Θ) : 0≤ radii i ∧ radii i ≤ R := by have h:= conventionSeparate; fin_cases i <;> simp [radii] <;> linarith
-- Core factors (scale stamp in slot 0 only)
def toll (t:Θ) (x:E4) : ℝ := (if t=0 then stamp else 1) * bellM (‖x‖^2-(radii t)^2)
private lemma toast (t:Θ) : ContDiff ℝ ∞ (toll t) := by unfold toll; exact contDiff_const.mul (bellM.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const))
variable (x : Fin m ↪ Θ)

def tranche (p:Points m) := (↑(∏ i,toll (x i) (p i)):ℂ)
private lemma smooth : ContDiff ℝ ∞ (tranche x) := Complex.ofRealCLM.contDiff.comp (contDiff_prod (t:=Finset.univ) (f:=fun i (z:Points m)=>toll (x i) (z i)) (fun i _ => (toast _).comp (PiLp.proj (p:=2) (𝕜:=ℝ) (β:=fun _:Fin m=>E4) i).contDiff))
private lemma range_to (u v:ℝ)(hu:0 ≤ u)(hv:0 ≤ v)(hx: |u^2-v^2| < 1) : |u-v| ≤1 := by
 obtain ⟨h₁,h₂⟩:=abs_lt.mp hx; rw [abs_le]; constructor <;> nlinarith
lemma rim : tsupport (tranche x) ⊆ ⋂ i:Fin m,{p:Points m | |‖p i‖-radii (x i)| ≤ 1} := by
  apply closure_minimal
  · intro p hp; apply Set.mem_iInter.mpr; intro i
    unfold Function.support tranche at hp
    have he := Finset.prod_ne_zero_iff.mp (Complex.ofReal_ne_zero.mp (show (tranche x p)≠0 from hp))  i (Finset.mem_univ i); have hh:= right_ne_zero_of_mul he; apply range_to _ _ (norm_nonneg _) (ordered _).1 (markM _ hh)
  apply isClosed_iInter; intro i; exact isClosed_le (((PiLp.proj (p:=2) (𝕜:=ℝ) (β:=fun _:Fin m=>E4) i).continuous.norm.sub continuous_const).abs) continuous_const
private lemma compact : HasCompactSupport (tranche x):=by
  let J := closedBall (0:E4) (R+1)
  have hc := (isCompact_univ_pi fun _ : Fin m=> (show IsCompact J from isCompact_closedBall ..)).image (PiLp.continuous_toLp 2 (fun _:Fin m=>E4))
  refine hc.of_isClosed_subset (isClosed_tsupport _) (fun p hp=> ?_)
  refine ⟨WithLp.ofLp p,fun i _=>?_,rfl⟩
  apply mem_closedBall_iff_norm.mpr; have hi:= Set.mem_iInter.mp (rim x hp) i; change ‖p i-0‖ ≤ _; rw [sub_zero]
  linarith only [(ordered (x i)).2,(abs_le.mp (show |‖p i‖-radii (x i)|≤1 from hi)).2]
lemma away (i j: Fin m) (hi:i≠j) (p:Points m)(hp:p∈tsupport (tranche x)) : 4 < ‖p i-p j‖ := by
  have hv(s t : Θ)(he:s≠t) : radii s ≥ radii t +9 ∨ radii t ≥ radii s+9:= by
    have hn:= conventionSeparate; fin_cases s<;>fin_cases t<;> simp_all [radii] <;> first | left; linarith | right; linarith
  have hj(i':Fin m):= abs_le.mp (show |‖p i'‖-radii (x i')| ≤1 from Set.mem_iInter.mp (rim x hp) i');
  obtain h|h:= hv _ _ (x.injective.ne hi);
  · linarith only [(hj i).1,(hj j).2,h,norm_sub_norm_le (p i) (p j)]
  rw [norm_sub_rev]; linarith only [(hj i).2,(hj j).1,h,norm_sub_norm_le (p j) (p i)]

def near : Test m:= ⟨tranche x,(smooth x).of_le (by decide),compact x,fun p hp i j he=> Classical.byContradiction (fun h=> by
   have hh:= away x i j h p hp; rw [show p i=p j from he,sub_self,norm_zero] at hh; norm_num at hh)⟩
lemma factor (p:Points 3) : profileChoice p=near (Function.Embedding.refl Θ) p := by
  change (↑(stamp * candid conventionRadius p):ℂ) = tranche _ p; unfold tranche; congr 1;
  simp [candid,Fin.prod_univ_succ,toll,radii,mul_assoc]

def tune (i:Θ) (j:Deck F 6):ℝ := ((deck F 6).repr (Pert.Triangle.basic F i) j).re
private lemma contour_sent (i:Θ) : realBar (Pert.Triangle.sent i) = (Pert.Triangle.sent (G:=G) i) := by
 apply Subtype.ext; apply eval_ext; intro A
 change Labels.read A (Labels.conjPol (sent i).val)= Labels.read A (sent i).val
 rw [Labels.conj_value]; unfold sent; split
 · change star (Labels.read A (Pert.Triangle.bFan G))= Labels.read A (Pert.Triangle.bFan G)
   rw [read_b]; simp
 · change star (Labels.read A (Pert.Triangle.uMinus G)) = Labels.read A (Pert.Triangle.uMinus G)
   rw [read_u]; simp
lemma contour (i:Θ) (j:Deck F 6) : (↑(tune F i j):ℂ)= (deck F 6).repr (Pert.Triangle.basic F i) j := by
  have hr : (freeTable F).conj (table_spin F) 6 (Pert.Triangle.basic F i)= Pert.Triangle.basic F i:= by
    apply writes_inj F 6; unfold Pert.Triangle.basic;
    simp only [comp_apply]; rw [writes_bar]; change barPol ((writes F 6) (Extra.FD.sourceAt F 6 (sent i))) = (writes F 6) (Extra.FD.sourceAt F 6 (sent i)); rw [_root_.YM.FormalOPE.RG10.Position.form F,← observe_bar,contour_sent]
  apply Complex.conj_eq_iff_re.mp
  let A:=Pert.Triangle.basic F i; let B:=deck F 6; let g(u):=starRingEnd ℂ (B.repr A u)
  have hh : ∑ k, g k • B k= A:= by
    have hx := congr_arg ((freeTable F).conj (table_spin F) 6) (B.sum_repr A)
    simp_rw [map_sum,map_smulₛₗ] at hx; simpa only [A,B,deck_real,hr] using hx
  have hy : B.repr (∑ k, g k • B k) j=g j := by rw [map_sum,Finsupp.finsetSum_apply]; simp [Finsupp.single_apply]
  rw [hh] at hy; exact hy.symm

def slope (G : Gauge):ℝ := ∫ p:Points 3,testReal p*Pert.Triangle.response G p
lemma slope_value : Pert.Triangle.cTest G=(↑(slope G):ℂ):=by
  unfold Pert.Triangle.cTest Test.applyTo slope; rw [← integral_complex_ofReal]; apply integral_congr_ae; filter_upwards with p; change (↑(stamp * testReal p):ℂ) * (↑(fullTransfer G p):ℂ)= (↑(testReal p*Pert.Triangle.response G p): ℂ); unfold Pert.Triangle.response; push_cast; ring
lemma pulse (h:G.Simple) : 0 < slope G:=Pert.Triangle.firstTestPositive h

end YM.FormalOPE.RG10.Position.Peal
