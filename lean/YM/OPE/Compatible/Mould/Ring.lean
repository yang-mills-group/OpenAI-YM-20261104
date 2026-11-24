import YM.OPE.Compatible.Mould.Germ
/-!
# Primal gear. on-shell polls.Wipe. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
open Labels WardBin
-- Rank grading. Smoke.Y. Glow
lemma ghost_iff (p:Bead G d e): p ∈ Ghost G d e ↔ ∀ i, wiped (impress p i).val:=by
     constructor
     · intro h i; apply (towel (d:=d+1) (impress p i)).2; intro T
       let f(j:Fin (e+1)):= (impress p j).val (fun _=>life T d); let g(j)(x:ℝ):= x^(j:Fin (e+1)).val • f j; suffices hx:f i=0 by exact hx
       have hP(x:ℝ): (∑ j,g j x)=0:=by
          let Y:Maxwell.TaylorTower G:=fun j=> x • T j; have ht: life Y d=x • life T d:=by funext j; unfold life Y; erw [map_smul]; rfl
          have hx:= (h Y); change master p Y =0 at hx; unfold master at hx; rw [ht] at hx; rw [← hx]; refine sum_congr rfl fun j _=>?_ ; let V:=impress p j; exact Eq.symm ((V.val.map_smul_univ (c:=fun _=>x) (m:=fun _=> life T d)).trans (by simp[g, f,V]))
       have hx: leading i.val (fun t:ℝ=> ∑ j,g j t)=0:=by simp_rw[hP]; simp [leading]
       rw [lead_sum (f:=g) _ (fun j _=> by unfold g; fun_prop)] at hx; simp_rw [g,lead_monomial] at hx; rw [sum_eq_single i] at hx;simpa using hx; intro j _ hj; rw [if_neg (fun h=> hj (Fin.ext h.symm))];simp
     intro hp T; apply sum_eq_zero; intro i _; exact (towel (d:=d+1) _).1 (hp i) T
lemma byPart (p:Bead G d e)(h:p∈ Ghost G d e)(i): Pi.single i (p i)∈ Ghost G d e:=by
      let q:= Pi.single (M:=fun i:Fin (e+1)=> TagW G d e i.val) i (p i); apply (ghost_iff _).2; intro j; by_cases hp:j=i; · subst j; rw [show impress q i= impress p i from by unfold impress q; erw [Pi.single_eq_same]]; exact ghost_iff p|>.1 h i
      intro t; rw [show impress q j=_ from (show impress q j=0 from by unfold impress;change (coordinateQ _ _ _ _).symm (q j)=_; rw [show q j=0 from Pi.single_eq_of_ne hp _,map_zero])]; rfl
-- cap
abbrev Crop (k:ℕ)(p:Tracts G d τ):Prop:=∀ i:ℕ,k≤ i→ lilies (τ 0) (d+(0:Phase).val) _ ((p 0).val) i=0
lemma Crop.plus {x y: Tracts G d τ}(h:Crop k x)(hp:Crop k y):Crop k (x+y):=fun i hi=> by erw[Pi.add_apply,Submodule.coe_add,map_add,Pi.add_apply, show _=_ from h i hi,show _=_ from hp i hi,add_zero]
lemma Crop.diff {x y: Tracts G d τ}(h:Crop k x)(hp:Crop k y):Crop k (x-y):=fun i hi=> by erw[Pi.sub_apply,Submodule.coe_sub,map_sub,Pi.sub_apply, show _=_ from h i hi,show _=_ from hp i hi,sub_self]
lemma Crop.Vert {x:Tracts G d τ}(h:Crop k x)(a:ℝ):Crop k (a • x):=fun i hi=> by change lilies _ _ _ (a • (x 0).val) i=0; rw [map_smul,Pi.smul_apply,h i hi,smul_zero]
lemma Crop.from {z:Tracts G d τ}(h:(z 0)=0): Crop k z:=fun i _=>by rw[h];erw [map_zero];rfl
lemma Crop.mono {z:Tracts G d τ}(h:Crop k z)(hp:k≤r): Crop r z:=fun _ he=> h _ (hp.trans he)
end YM.OPE.Stroke
