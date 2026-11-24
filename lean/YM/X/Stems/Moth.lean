import YM.X.Stems.Iota
import YM.PertExtension.MixedRule
import YM.PertExtension.VertexSymbol
import YM.PertExtension.PlateEvaluation
import YM.Pert.Lattice.Plate
/-!
## Authentic first mark formula: seeing minimum slot. Reality and uniform stencil support.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open PertExtension.Heat.Top Next.Rank.Normal MvPolynomial Finsupp
open Source ProjectorNext.Calibration Gauss PertExtension.Series.Tested
open Gauge Labels Bid LatticePT
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {s:Finset Cover} {d:ℕ} {F:Labels.Frame G d}
variable (x : Brush G)
def curl (x:Brush G)(y:Cover)(a b:Axis) := x (y,a) + x (y+step a,b)-x (y,b)- x (y+step b,a)
def v (x:Brush G) (p:RG.Slot): G.Color:= curl x p.offset p.plaq.val.1 p.plaq.val.2
lemma link_deriv (p:Pin): HasDerivAt (fun r:ℝ=>G.mat (posit (r • x) p)) (G.colorMat (x p)) 0:= by
   change HasDerivAt (fun r:ℝ=>G.mat (G.lieExp (r • x p))) _ _ ; simp only [G.mat_lieExp,map_smul]; simpa using! (hasDerivAt_exp_smul_const (G.colorMat (x p)) (0:ℝ))
@[simp] lemma posit_flat {G:Gauge}: posit (0:Brush G)=1:= by funext i; unfold posit; apply G.mat_injective; simp
lemma curl_deriv (p:Cover)(i j:Axis): HasDerivAt (fun r:ℝ=>G.mat (travel (posit (r • x)) p (square i j))) (G.colorMat (curl x p i j)) 0 := by
   simp_rw [Pert.Bare.square_links,G.mat_mul,G.mat_inv]; apply ((((link_deriv x (p,i)).mul (link_deriv x _)).mul (link_deriv x _).star).mul (link_deriv x (p,j)).star).congr_deriv; simp only [zero_smul, posit_flat, Pi.one_apply, mat_one,star_one,one_mul,mul_one,colorMat_skew,curl,map_add,map_sub,Pi.mul_apply]; abel
lemma curls (p:Cover)(i j:Axis): HasDerivAt (fun r:ℝ=>G.curvature (travel (posit (r • x)) p (square i j))) (curl x p i j) 0 := by
   let w:= (curl_deriv x p i j); simp_rw [Gauge.curvature,G.mat_inv]; apply HasDerivAt.congr_deriv (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ((w.sub w.star).const_smul ((1/2):ℝ)))
   change G.projectColor (((1/2):ℝ) • (G.colorMat _ - star (G.colorMat _)))= _; rw [G.colorMat_skew,sub_neg_eq_add, ← two_smul ℝ,smul_smul]; norm_num
lemma traveled (p:RG.Slot):HasDerivAt (fun r:ℝ=>p.eval (posit (r • x))) (v x p) 0:= by
    let A(t:ℝ):=G.mat (travel (posit (t•x)) 0 p.walk)
    let B(t:ℝ):=G.curvature (faceValue (posit (t•x)) (p.offset,p.plaq))
    obtain ⟨s,hs⟩ := Small.path (G:=G) p.walk 0
    have h : HasDerivAt A (deriv A 0) 0 := (hs.substituted (T:=fun t:ℝ=> posit (t • x)) (fun i=> G.exp_jet.contDiffAt.comp (f:=fun t:ℝ=>t • x i.val) _ ((contDiff_id (𝕜:=ℝ) (E:=ℝ)).contDiffAt.smul contDiffAt_const))).differentiableAt (by simp) |>.hasDerivAt
    have hb : HasDerivAt B (v x p) 0:= curls ..
    have ht : A 0=1:= by simp [A,Pressure.one]
    have ht' : B 0=0:= by simp [B,faceValue,Pressure.one]
    refine (HasDerivAt.congr_deriv (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ((h.mul (G.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hb)).mul h.star)) ?_); simp [ht,ht',Pressure.one]; exact G.project_colorMat _

def arc (k:G.ColorIndex)(p:Cover)(i j:Axis) : Hair G→₀ ℝ:=
   Finsupp.single ((p,i),k) 1+Finsupp.single ((p+step i,j),k) 1-Finsupp.single ((p,j),k) 1-Finsupp.single ((p+step j,i),k) 1
def com (a:Hair G→₀ℝ) : Hair G→₀ ℂ:= Finsupp.linearCombination ℝ (fun i:Hair G=> Finsupp.single i 1) a
lemma com_six (i:Hair G)(k:ℝ): com (Finsupp.single i k)=Finsupp.single i (k:ℂ):= by unfold com;rw [linearCombination_single,smul_single]; simp
lemma com_text (p : Hair G→₀ℝ) : Next.Rank.Normal.glyph (com p)=blade p:= by -- Normal qualified?
   induction p using Finsupp.induction_linear with
   | zero=> simp [Next.Rank.Normal.glyph,com,blade]
   | add a b h g=> unfold com blade at *; rw [_root_.map_add,_root_.map_add,h,g,_root_.map_add]
   | single i c=> simp only [com_six,Next.Rank.Normal.glyph,linearCombination_single,blade, linearCombination_single]; simp
lemma arc_eq (k : G.ColorIndex) (p:Cover)(i j:Axis): linearCombination ℝ (text x) (arc k p i j)=curl x p i j k:= by
   simp only [arc,map_sub,map_add,linearCombination_single,one_smul]; rfl

def iris (a:Atom G): Hair G→₀ ℝ:= arc a.2 a.1.offset a.1.plaq.val.1 a.1.plaq.val.2
def loom : poly (Atom G) →ₐ[ℂ] Curly G:= exchange (com ∘ iris)
lemma looms (p:poly (Atom G)): snap x (loom p)=aeval (fun i:Atom G=> (v x i.1 i.2 :ℂ)) p:= by
   apply DFunLike.congr_fun (f:=(snap x).comp loom); ext i; simp only [AlgHom.comp_apply,aeval_X,loom,exchange_x]; rw [Function.comp_apply,com_text,snaps_blade]; exact congr_arg Complex.ofReal (arc_eq ..)

def evalS (S:SectionData F)(i:F.Index)(U:CoverConfig G):= (S.evaluate (Pi.single i 1) U).re
variable {H:Hol G} {S:SectionData F}
variable (i:F.Index) (h:S.Sound H)(P:pop S)
include h
lemma eval_true (U:CoverConfig G): (evalS S i U :ℂ)= S.evaluate (Pi.single i 1) U:= by -- include h
   have hx : star (Pi.single i 1:F.Coeff)=Pi.single i 1:= by funext j; simp [Pi.single_apply]
   have he:= h.ordinary_real (Pi.single i 1) U; rw [hx] at he; exact Complex.conj_eq_iff_re.mp he.symm
private abbrev E:= (rendered S P).toData
include P
lemma opt : Small G (evalS S i):= by
   rw [show evalS S i= Complex.re ∘ S.evaluate (Pi.single i 1) from rfl, (rend_acts h P) i]; exact ((Small.vector _ (fun j: Fin ((E P).count i)=> Small.slot _)).comp (L:=lumin ((E P).shape i)) (smooth_lumin _)).comp Complex.reCLM.contDiff

section
include h P
private abbrev w:= (F.grades i).2
lemma appears : Tendsto (fun t:ℝ=> t⁻¹^w i * along (evalS S i) x t) Tested.germ (𝓝 (snap x (loom ((topMatrix S H h P).basis i))).re) := by
   let j := w i ; let D:=(rendered S P).toData; let W:=topMatrix S H h P
   let q(t:ℝ):Drops.GaugePanel G (D.count i):=fun k=> (D.columns i k).eval (posit (t • x))
   let z:= v x ∘ D.columns i
   have he : along (evalS S i) x=(fun t=>(lumin (D.shape i) (q t)).re) := funext fun t=>congr_arg Complex.re (show S.evaluate _ _ = _ from by rw [(rend_acts h P i)];rfl)
   have hh := Slope.isolate (D.shape i) (D.low i) q z (fun k=> ?eq)
   case eq =>
      let f(t:ℝ):= q t k.1 k.2
      have h : HasDerivAt f (z k.1 k.2) 0:= (EuclideanSpace.proj (𝕜:=ℝ) k.2).hasFDerivAt.comp_hasDerivAt 0 (traveled x (D.columns i k.1))
      convert! h.tendsto_slope_zero_right using 2; simp only [f,q, zero_add, zero_smul,posit_flat,RG.Slot.eval,faceValue,Pressure.one,G.curvature_unit,map_zero,PiLp.zero_apply,sub_zero];rfl -- edit
   have hv := Complex.continuous_re.continuousAt.tendsto.comp hh
   convert! hv using 2
   · rw [Function.comp_apply,he,← Complex.ofReal_inv,←Complex.ofReal_pow];simp only [Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
   rw [looms]; unfold LatticePT.topMatrix Heat.Top.topFrame Heat.Top.raw Heat.Top.rawPart; rw [aeval_rename];rfl
lemma leading_asp : Aspiration (along (evalS S i) x) (Jet.someJ (along (evalS S i) x)):= by
   obtain ⟨s,hs⟩:=opt i h P; have hk:ContDiffAt ℝ ∞ (kind s (evalS S i)) 0:= (kinds hs).of_le le_top; have he:= directions hk (comb x); rw [← along_kind hs x] at he; exact (show Jet.someJ _=(fun j=> jet _ j _) from funext fun j=> stamp_at hs x j) ▸ he -- dir
lemma no_under {j:ℕ}(hj:j< (F.grades i).2): Jet.someJ (along (evalS S i) x) j=0 := by
   let a:=along (evalS S i) x; let p:=snap x (loom ((topMatrix S H h P).basis i))
   apply (leading_asp x i h P).vanish (w:=w i) _ hj; refine ⟨‖p.re‖+1,by positivity,?_⟩
   filter_upwards [(appears x i h P).norm.eventually (eventually_le_nhds (lt_add_one ‖p.re‖)),Tested.eventually_pos] with t ht hp
   rw [norm_mul,Real.norm_of_nonneg (pow_nonneg (inv_pos_of_pos hp).le _), inv_pow, inv_mul_eq_div] at ht; exact (div_le_iff₀ (pow_pos hp _)).mp ht
lemma basis_moon : loom ((topMatrix S H h P).basis i) = mark (evalS S i) (opt i h P) (w i):= by
   apply snap_ext; intro x
   have he : Jet.someJ (along (evalS S i) x) (w i)=(snap x (loom ((topMatrix S H h P).basis i))).re:= tendsto_nhds_unique (((leading_asp x i h P).shift (fun j hj=> no_under x i h P hj)).tendsto_first) (appears x i h P) -- num+0
   rw [mark_test,he]
   let X:=(topMatrix S H h P).basis i
   rw [looms]; exact (Complex.conj_eq_iff_re.mp ((LatticePT.Vertex.basis_real S H h P i) (v x))).symm
end
end YM.PositionX.Stems
