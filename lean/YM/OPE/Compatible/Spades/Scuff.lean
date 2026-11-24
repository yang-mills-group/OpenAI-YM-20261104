import YM.OPE.Compatible.Sward.Lux
import YM.OPE.Compatible.Spades.Pine
import YM.OPE.Compatible.Spades.Lores
import YM.OPE.Compatible.Scrape.Slick
/-!
# Cappuccino local Gaussian supports, color prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
abbrev Fpaper (G:Gauge)(b:ℕ):= TilesB b× G.ColorIndex
abbrev Scoop (G:Gauge)(b:ℕ):= PAD (Fpaper G b)
noncomputable def strideG (G:Gauge)(b:ℕ): DrawerB G b≃L[ℝ] Scoop G b:= LinearEquiv.toContinuousLinearEquiv {
       toFun v i:= v i.1 i.2
       invFun v i:= WithLp.toLp 2 (fun j=> v (i,j))
       map_add' _ _:=rfl
       map_smul' _ _:=rfl
       left_inv _:=rfl
       right_inv _:=rfl }
lemma strideSize (G:Gauge):∃ C:ℝ, 1≤C∧∀ i, ‖(strideG G i).toContinuousLinearMap‖≤C∧‖(strideG G i).symm.toContinuousLinearMap‖ ≤ C:=by
       let F :(G.ColorIndex→ℝ)→ₗ[ℝ] G.Color:= {toFun:=WithLp.toLp 2,map_add' x y:=rfl,map_smul' t x:=rfl} -- edit
       let L : (G.ColorIndex→ℝ)→L[ℝ] G.Color:= F.toContinuousLinearMap; let C:=max 1 ‖L‖; have he:1≤C:=le_max_left ..; have hV:0 ≤ C:=zero_le_one.trans he; refine ⟨C,he,fun i=>⟨?_,?_⟩⟩
       · refine (strideG G i).toContinuousLinearMap.opNorm_le_bound hV (fun x=> (pi_norm_le_iff_of_nonneg (mul_nonneg hV (norm_nonneg x))).2 (fun j=> ((PiLp.norm_apply_le (x j.1) j.2).trans (norm_le_pi_norm x j.1)).trans (le_mul_of_one_le_left (norm_nonneg _) he)))
       refine (strideG G i).symm.toContinuousLinearMap.opNorm_le_bound hV (fun x=> (pi_norm_le_iff_of_nonneg (mul_nonneg hV (norm_nonneg x))).2 fun j=> ((L.le_opNorm (fun y=>x (j,y)))).trans (mul_le_mul (le_max_right ..) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun y=> norm_le_pi_norm x (j,y)) (norm_nonneg _) hV))
local notation "GJ"=>Vec G n 1
abbrev ascJ (o:Site n):Vec G n 1→ₗ[ℝ] fieldX (Shade G):= { toFun := fun v=> upl o (deckW G n v),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
noncomputable def scanf (G:Gauge)(b:ℕ)(o:Site n):Vec G n 1→L[ℝ] DrawerB G b:= (InLine b ∘ₗ ascJ o (G:=G)).toContinuousLinearMap
noncomputable def VScan (G:Gauge)(b:ℕ)(o:Site n):Vec G n 1→L[ℝ] Scoop G b:= (strideG G b).toContinuousLinearMap ∘L (scanf G b o)
noncomputable def floss (G:Gauge)(b:ℕ)(o:Site n):Vec G n 1→L[ℝ] Scoop G b:= (strideG G b).toContinuousLinearMap ∘L (socket b ∘L scanf G (4*b) o)
noncomputable abbrev Fport (C:KernelChoices)(v:Train i)(G:Gauge)(n:Side)(h:4 ≤ i) := (Vessel C v G n h)
lemma HeatZ {v:Train i}(h:4 ≤ i)(x: Vec G n 1)(hp: Prog K v G n *ᵥ x=0):∃ u:fieldX G.ColorIndex, ascJ o x= mountain u:=by
       have hx(j:G.ColorIndex):d 1 n *ᵥ component x j=0:= by
            have ht: Precision.K ((pink K.penalty v).acts n)*ᵥ component x j=0:=by rw[← component_mul,hp];rfl
            exact (curtain0 v h (K:=K) _).1 ht
       choose P hP using fun j=> origins (component x j) (hx j)
       -- define manually
       let f:fieldX G.ColorIndex:= fun i=>∑ j:Axis,(i.1 j:ℤ)*(missing n *ᵥ component x i.2) (0,coord j); let g:deck G.ColorIndex n:= fun p=>P p.2 (p.1,vac); let q:=f+upl o g
       have hz(j:Cover × Shade G): mountain f j =(missing n*ᵥ component x j.2.2) (o+wrap n j.1,coord j.2.1):=stairs x j o
       refine ⟨q, funext fun j=>?_⟩; let u:=o+wrap n j.1; change component x j.2.2 (u,coord j.2.1)=q _-q _; rw[hP]; change _+(d 0 n *ᵥ _ ) (u,coord j.2.1)=_; rw[d_sites]; unfold q; rw[Pi.add_apply,Pi.add_apply,add_sub_add_comm,show f _-f _= _ from hz j]; unfold upl; rw [map_add, wrap_step, ←add_assoc]
lemma flareK (K:KernelChoices)(x:Train i)(hp:4 ≤ i)(u:Vec G n 1)(he:Prog K x G n*ᵥu=0)(b:ℕ): floss G b o u=0:=by
      obtain ⟨v,h⟩:= HeatZ o hp u he; change strideG G b (socket b (InLine (4*b) (ascJ o u)))=_; rw[h,blown,map_zero]
end YM.OPE.Spells
