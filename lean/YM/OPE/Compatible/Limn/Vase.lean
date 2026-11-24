import YM.OPE.Compatible.Limn.Cheek
/-! # W basis.Real stencil. Mixed resource entries -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
open Green(wt)
section
abbrev Wings (G:Gauge)(c:Side):= Body 1 c × G.ColorIndex
def cotW (S:StepData c f)(x:Wings G c):= S.ratio.embed x.1.1
noncomputable def JetB (G:Gauge)(c:Side):= Tip G (Body 1 c)
lemma suit (x:Wings G c):JetB G c x=Pi.single x.1 (EuclideanSpace.basisFun G.ColorIndex ℝ x.2):= by unfold JetB Tip; rw [Basis.reindex_apply, Pi.basis_apply]; rfl
lemma cashBed (x:Wings G c)(i:Site f): Radius.Showroom.outer S G t i (JetB G c x) (wt t i (cotW S x))⁻¹:=by
         intro j; by_cases hj:j=x.1
         · subst j; rw [suit,Pi.single_eq_same,OrthonormalBasis.norm_eq_one,Green.wt_symm]; change 1 ≤ (wt t (cotW S x) i)⁻¹*wt t (cotW S x) i; rw [inv_mul_cancel₀ (Green.wt_pos ..).ne']
         rw [suit, Pi.single_eq_of_ne hj, norm_zero]; exact mul_nonneg (inv_nonneg.mpr (Green.wt_pos ..).le) (Green.wt_pos ..).le
lemma prepMint (S:StepData c f)(F:Forest S.ratio)(x:Key F G): Purchase.slew S F x=(0,countingBasis F G x):=by rw[countingBasis_apply];rfl
abbrev Vθ (S:StepData c f)(F:Forest S.ratio)(G:Gauge):= Wings G c ⊕ Key F G
noncomputable def MintS (S:StepData c f)(F:Forest S.ratio)(G:Gauge):Basis (Vθ S F G) ℝ (Bid.Dir G c ×AxisChart G F):= (JetB G c).prod (countingBasis F G)
noncomputable def δV (S:StepData c f)(F:Forest S.ratio)(x:Vθ S F G):= Sum.elim (cotW S (G:=G)) (pointK S F) x
lemma Dhome (x: Vθ S F G)(i:Site f): Radius.Showroom.On S F G t i (MintS S F G x) (wt t i (δV S F x))⁻¹:=by
      rcases x with x|x
      · rw [MintS,Basis.prod_apply,Sum.elim_inl]; exact ⟨cashBed x i, zeroed _ _ _ _ (inv_nonneg.mpr (Green.wt_pos ..).le)⟩
      rw [MintS,Basis.prod_apply,Sum.elim_inr]; change On S F G t i (0,countingBasis _ G x) _; rw [← prepMint]; exact Purchase.allows S F x ..
abbrev creep (G:Gauge) (t:ℝ):= (((Fintype.card (TypeFace 1):ℝ)*Premium.overall t)*(Fintype.card G.ColorIndex))
lemma oro (S:StepData c f)(ht:0<t)(x:Site f): ∑ i: Wings G c, Wisps.rate (-t) (separation x (cotW S i)) ≤ creep G t:=by
       have hg: ∑ i:Site c,(wt t (S.ratio.embed i) x)⁻¹ ≤ Premium.overall t:=by
          let e: Site c↪ Site f:= ⟨S.ratio.embed,fun i j hz=>by have he:=congr_arg S.ratio.parent hz; rw[S.ratio.embed_parent,S.ratio.embed_parent] at he; exact he⟩
          change ∑ i,(wt t (e i) x)⁻¹≤_; rw [←Finset.sum_map (f:=fun u=>(wt t u x)⁻¹) _ e]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>inv_nonneg.mpr (Green.wt_pos ..).le)).trans (by simpa using Premium.lives 1 ht x)
       change ∑ i: (Site c × TypeFace 1) × G.ColorIndex, Real.exp (-t*separation x (S.ratio.embed i.1.1)) ≤ _; rw [Fintype.sum_prod_type]; simp_rw [neg_mul,Real.exp_neg,sum_const,nsmul_eq_mul,card_univ,←mul_sum,Fintype.sum_prod_type]; simp_rw[sum_const,nsmul_eq_mul,card_univ, ←mul_sum,separation_comm x]; rw [creep,mul_comm _ (Fintype.card G.ColorIndex:ℝ)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
lemma galore (S:StepData c f)(F:Forest S.ratio)(ht:0<t)(x:Site f): ∑ i: Vθ S F G, Wisps.rate (-t) (separation x (δV S F i)) ≤ creep G t+farm G t:=by unfold Vθ;rw [Fintype.sum_sum_type];exact add_le_add (oro S ht x) (farmPay S F ht x)
noncomputable def Bitush (S:StepData c f)(F:Forest S.ratio) (u:Bid.Dir G c ×AxisChart G F→ℝ) (i j:Vθ S F G):= iteratedFDeriv ℝ 2 u 0 ![MintS S F G i,MintS S F G j]
lemma lensM {p:Site f→(Bid.Dir G c ×AxisChart G F)→ℝ}{U:Bid.Dir G c ×AxisChart G F →ℝ} (ht:0<t)(hB:0≤R) (he:0<ε)(hx:Dew.Pile S F ε R t m U p)(hm:2 ≤ m)(i j:Vθ S F G): wt (t/2) (δV S F i) (δV S F j)*|Bitush S F U i j| ≤ R*Premium.overall (t/2):=by
              let Z:= MintS S F G; let a:=δV S F i; let b:=δV S F j; let A:=wt (t/2) a b; have hh: ‖(0:Bid.Dir G c × AxisChart G F)‖ < ε:=by rw[norm_zero];exact he
              unfold Bitush; change A*_ ≤_; rw [hx.dunk hh,_root_.sum_apply]; apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (Green.wt_pos ..).le).trans; rw [mul_sum]; refine (sum_le_sum (g:=fun j:Site f=>R*(wt (t/2) j a)⁻¹) (fun y _=>?_)).trans ?_
              · let w(k:Fin 2):=(wt t y (δV S F (![i,j] k)))⁻¹; let f': Fin 2→ Vθ S F G:=![i,j]; have h:= hx.voice y 0 hh 2 hm (fun k=>Z (f' k)) w (fun l=>⟨inv_nonneg.mpr (Green.wt_pos t y (δV S F (f' l))|>.le),Dhome _ _⟩); rw [show ![MintS _ _ _ i,MintS _ _ _ j]=(fun k=>Z (f' k)) from funext fun k=>by fin_cases k<;>rfl]; rw [Fin.prod_univ_two] at h; apply (mul_le_mul_of_nonneg_left (show _ from h) (Green.wt_pos ..).le).trans; change wt (t/2) a b*(R*((wt t y a)⁻¹ * (wt t y b)⁻¹))≤_; rw [mul_left_comm, Green.wt_symm t y a,Green.wt_symm t y b]
                exact mul_le_mul_of_nonneg_left ((show (wt _ a b)*_ ≤ (wt (t/2) _ _)⁻¹ from eaten a b y ht)) hB
              rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (by simpa using Premium.lives 1 (half_pos ht) a) hB
end
end YM.OPE.Limn
