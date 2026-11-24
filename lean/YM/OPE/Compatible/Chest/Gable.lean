import YM.OPE.Compatible.Sward.Can
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Degree cutoffs and extension of bounded families

`Cap` keeps the components of degree less than `d` and sets the rest to zero.
`CapLate` shows that subtracting this projection leaves a vector whose
components below `d` vanish. For a finite-dimensional target and `1 ≤ Y`,
`uplift` extends a family of continuous linear maps from a submodule to the
whole space while retaining a uniform polynomial norm bound in `Y`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section bins
open Silt.Phere
noncomputable def Cap (I:Type)(d k m:ℕ):Seat k m I→L[ℝ] Seat k m I:= ContinuousLinearMap.pi fun i:Fin (k+1)=> if i.val<d then ContinuousLinearMap.proj i else 0
lemma crimp (p:Seat k m I) : lilies m k I (Cap I d k m p) i= if i < d then lilies m k _ p i else 0:=by
        by_cases ht:i≤k
        · rw [soup,soup]; unfold moduleAt; rw [dif_pos ht]; let f:Fin (k+1):=⟨i,by omega⟩; change seed m i I (Cap I d k m p f)= _; unfold Cap; rw [ContinuousLinearMap.pi_apply]; by_cases he:i<d; rw [if_pos (show f.val<d from he),if_pos he] 
          rw [if_neg (show ¬ f.val<d from he),if_neg he]; exact map_zero _
        rw [(sproutV _ _ _).1 _ (by omega),(sproutV _ _ _).1 _ (by omega)]; simp
lemma cap_erode (p:Seat k m (Shade G))(hp:p∈bed G k m) (d:ℕ):Cap _ d k m p∈bed G k m:=fun i=>by
        rw [crimp]; split; exact hp _; exact (cope G i m).zero_mem
noncomputable def Ov (G:Gauge)(d k m:ℕ):bed G k m→L[ℝ] bed G k m:= (Cap (Shade G) d k m ∘L (bed G k m).subtypeL).codRestrict _ (fun x=>cap_erode x.val x.property d)
lemma CapLate (V:Seat k m I)(d:ℕ): Deep (m:=m) (V-Cap I d k m V) d:=fun i hi=>by rw[map_sub,Pi.sub_apply, crimp, if_pos hi,sub_self]
lemma CapStone (V:Seat k m I)(h:Deep (m:=m) V d) : Cap I d k m V=0:=lilies_inj I k m (funext fun i=>by rw [crimp,map_zero]; by_cases hh:i< d; rw [if_pos hh,h i hh];rfl; rw[if_neg hh];rfl)
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
lemma uplift (p:Submodule ℝ E)(f:M→ p→L[ℝ] F)(h:Wealth f Y 1)(hy:1 ≤ Y) : ∃ g:M→ E→L[ℝ] F, Wealth g Y 1 ∧ ∀ m x, g m (x:p).val=f m x:=by
       let V:=Fin (Module.finrank ℝ F); let T:F≃L[ℝ] (V→ℝ):= (Module.finBasis ℝ F).equivFunL; let X:= T.symm; let S(i:V):= ContinuousLinearMap.proj i ∘L T.toContinuousLinearMap; choose A ha hA using fun i:V=> fun m=> exists_extension_norm_eq p (S i ∘L f m)
       let W(j):= ContinuousLinearMap.pi (fun i=> (A i j:E→L[ℝ] ℝ)); have hv:Brim W W Y 1:=by
           apply Wπ hy zero_le_one; intro i; apply soloWe; obtain ⟨c,hc,k,hT⟩:= PledgeW (f:=fun _=>S i) (wealthC _) h; refine ⟨c,hc,k,fun j=>?_⟩; change ‖ContinuousLinearMap.proj i ∘L W j‖≤_; rw [show _= A i j from (show ContinuousLinearMap.proj i ∘L W j=A i j from rfl),hA]; exact hT j
       refine ⟨fun j=> X.toContinuousLinearMap ∘L W j,PledgeW (wealthC _) hv.A,fun v y=>?_⟩; rw [ContinuousLinearMap.comp_apply]; rw [show W v y.val=T (f v y) from funext fun i=>ha i _ _]; exact T.symm_apply_apply _
end bins
end YM.OPE.Stroke
