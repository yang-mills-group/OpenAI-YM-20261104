import YM.OPE.Compatible.Gems.Five
/-! # Roots of curvature. finite-Ar.Ply.E -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
noncomputable def Vega (p:RodZ L k)(x:L.DirA):ℝ:= ∏ i:Fin k, LitA L x (p i)
noncomputable abbrev Dtn {f:Side}(x y:Site f):ℝ:= separation x y
noncomputable abbrev Wct (i:Drive L):= δV L.Z L.ForestQ i
noncomputable def Inrange (p:Site L.f)(r:RodZ L k):ℝ:=∑ i:Fin k,Dtn p (Wct L (r i))
lemma Win_go (p:Site L.f)(r:RodZ L k)(i:Fin k): Dtn p (Wct L (r i)) ≤ Inrange L p r :=single_le_sum (f:=fun j=> Dtn p (Wct L (r j))) (a:=i) (fun _ _=> Nat.cast_nonneg _) (mem_univ _)
lemma Win_hi (p:Site L.f)(r:RodZ L k):0≤ Inrange L p r:=sum_nonneg (fun _ _=> Nat.cast_nonneg _)
abbrev PinS (L:Host K T)(k:ℕ):=Site L.f→ RodZ L k →ℝ
structure Yields (f:L.DirA→ℝ)(k:ℕ)(p:PinS L k)(t s:ℝ):Prop where
       pos : 0 ≤ t
       pays (x:L.DirA): f x=∑ z:Site L.f,∑ i,p z i*Vega L i x
       dock (z:Site L.f)(i:RodZ L k): ‖p z i‖≤ t*Real.exp (-(s*Inrange L z i))
-- sums and bounding
abbrev Tires (L:Host K T)(f:L.DirA→ℝ)(k:ℕ)(s t:ℝ):Prop:= ∃ p,Yields L f k p s t
section
variable {p q:L.DirA→ℝ}
lemma nTires (h:Tires L p k s t): Tires L (-p) k s t:=by
       obtain ⟨x,h⟩:=h; refine ⟨-x,h.pos,fun i=>?_,fun i j=>?_⟩; · simp only[Pi.neg_apply,neg_mul,sum_neg_distrib,h.pays]
       simp only[Pi.neg_apply,norm_neg]; exact h.dock ..
lemma FTires (h:Tires L p k s t)(hv:Tires L q k u t):Tires L (p+q) k (s+u) t:=by
       obtain ⟨a,h⟩:=h; obtain ⟨b,hp⟩:=hv; refine ⟨a+b,add_nonneg h.pos hp.pos,fun i=>?_,fun i j=>?_⟩; · simp only [Pi.add_apply,h.pays,hp.pays,add_mul,sum_add_distrib]
       rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (h.dock ..) (hp.dock ..))
end
variable (f:L.DirA→ℝ)
noncomputable abbrev pricZ (i:RodZ L k):= (↑(k.factorial):ℝ)⁻¹* iteratedFDeriv ℝ k f 0 (MintS L.Z Fθ G ∘ i)
lemma Endorse (v:L.DirA) (k:ℕ):jet f k v=∑ i:RodZ L k, pricZ L f i* Vega L i v:=by
       let A:=MintS L.Z Fθ G; let P:= iteratedFDeriv ℝ k f 0; let F:= Finset.univ (α:=Drive L); unfold jet; have hv:P (fun _=>v)= ∑ i:RodZ L k,P (A ∘ i)*(∏ j:Fin k,LitA L v (i j)):=by
           have hp: (fun _:Fin k=>v)=fun _=> ∑ i:Drive L,LitA L v i • A i:=funext fun _=> (A.sum_repr _).symm; rw [hp,show P _= _ from P.map_sum_finset (fun _ (i:Drive L)=>LitA L v i • A i) (fun _=>F),show Fintype.piFinset (fun _:Fin k=>F)= (Finset.univ:Finset (RodZ L k)) from (by ext; simp [F])]; refine Finset.sum_congr rfl (fun i _=>?_); rw [show P (fun j=>LitA L v (i j) • A (i j))= _ from P.map_smul_univ (fun j=>LitA L v (i j)) (fun j=>A (i j)),smul_eq_mul]; exact mul_comm ..
       change _⁻¹* P _=_; rw [hv,mul_sum]; exact Finset.sum_congr rfl fun i _=> mul_assoc .. |>.symm
open Dew AnalyticNext.QuarticMatch Radius Radius.Showroom Progress.StationaryScenes
variable {g:Site L.f→ L.DirA→ ℝ}
lemma Kea (h:Dew.Pile L.Z L.ForestQ t C s m f g)(hh:k ≤ m)(hv:0 ≤ C)(ht:0<t): Tires L (jet f k) k C s:=by
          let p(i)(x:RodZ L k):= pricZ L (g i) x; have he : ‖(0:L.DirA)‖<t:= norm_zero.trans_lt ht; refine ⟨p,hv,fun x=>?_,fun i j=>?_⟩
          · rw [show jet f k x=∑ i:Site L.f,jet (g i) k x from ?_]; exact Finset.sum_congr rfl fun i _=> Endorse L (g i) x k
            simp_rw [jet,h.dunk he,_root_.sum_apply,mul_sum]
          unfold p pricZ; rw [norm_mul]; refine (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _)))).trans ?_; let u:=fun k=> (Green.wt s i (Wct L (j k)))⁻¹; have hU:= h.voice i _ he k hh (MintS _ _ _ ∘ j) u (fun k=>⟨inv_nonneg.mpr (Green.wt_pos _ i (Wct L (j k))|>.le), Dhome (S:=L.Z) (j k) i⟩); exact hU.trans_eq (congr_arg _ (show (∏ k,u k)= _ from (by unfold u Green.wt Inrange Dtn; rw [mul_sum,←sum_neg_distrib,Real.exp_sum]; apply prod_congr rfl; intro i hi; rw [Real.exp_neg]))) -- sign
end
end YM.OPE.Borealis.Galea
