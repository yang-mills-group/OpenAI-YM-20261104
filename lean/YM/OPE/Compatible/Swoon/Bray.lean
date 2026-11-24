import YM.OPE.Compatible.Swoon.Oort
/-!
# Parse graph cast. W hat reads true score/T-jets with sculpted weight Fskin(H). Need convert H-axis tax to covering. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r) {P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
def LumL : Kv × Qµ≃(forest S.ratio he).Free where
   toFun p:= trainV S he H p.1 (innerB S he H p.2)
   invFun i:= ((edgesK μ).tick i.val, home S he H i)
   left_inv:= by
       rintro ⟨i,p⟩; refine Prod.ext ?_ (by dsimp only; simp only [home_rot,home_inner]); change (edgesK μ).tick ((edgesK μ).go i p.val.val)= i; simp only [See.tick_go, See.tick_here,add_zero]
   right_inv:=padV S he H
open Pilot
lemma treeTax (x:LK): looper P x=looper P (prL V! G x)+looper P (prR V! G x):=by
      unfold looper; rw [← Equiv.sum_comp (valley S he H X).symm,Fintype.sum_sum_type]; rfl
include ht
lemma taxCabin : looper P (I:=Qµ) =ᶠ[𝓝 0] fun x=> taxY X! P (EchoV S he H G x) / 4:=by
     filter_upwards [Metric.ball_mem_nhds (0:J!) ht.patch] with x hx
     have hl(j:Qµ): x j∈ Metric.ball 0 P.radius:=by rw [ball_pi _ ht.patch] at hx; exact hx j (Set.mem_univ _)
     let v:=EchoV S he H G x; have hh: taxY X! P v=4*looper P x:=by
           unfold taxY looper; rw [← Equiv.sum_comp (LumL S he H),Fintype.sum_prod_type]; rw [show (∑ i:Kv,∑ j:Qµ,rake P (v (LumL S he H (i,j))))=∑ _i:Kv, ∑ j:Qµ,Real.log (P.J (x j)) from ?_, Finset.sum_const,Finset.card_univ,kvCard,nsmul_eq_mul,Nat.cast_ofNat]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>by
               change rake P (v (trainV S he H i (innerB S he H j))) = _; unfold v; rw [echoVi,home_rot,home_inner]; split
               next h=> exact congr_arg Real.log (Next.SectorChange.ratio_even ht (hl j)).symm -- orientation
               next h=> rfl
     rw [show taxY X! P (EchoV S he H G x)= _ from hh];ring
lemma billLoop (x:LK): Radial.jet (looper P) 2 x= Radial.jet (looper P) 2 (prL V! G x)+Radial.jet (taxY X! P) 2 (lamps S he H X G x).2 /4:=by
      let Z:P!→ℝ:= looper P; let D:= (4:ℝ)⁻¹ • taxY X! P;let L:=prL V! G; let Y':= EchoV S he H G∘L prR V! G; have hE:looper P=ᶠ[𝓝 (0:LK)] (Z ∘ L)+(D∘ Y'):=by
         have hp: Tendsto (prR V! G) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! (prR V! G).continuous.tendsto 0
         filter_upwards [hp.eventually (taxCabin S he H ht)] with i (hi:looper P (prR V! G i)=_); rw [treeTax,hi]; change Z (L i)+taxY X! P (Y' i)/4= Z (L i)+(4:ℝ)⁻¹ * taxY X! P (Y' i); ring
      have hu : ContDiffAt ℝ ω Z 0:= (pals _ ht).1; have hz:= (accountV X! ht).1; have hx:ContDiffAt ℝ ω D 0:=hz.const_smul (4:ℝ)⁻¹; rw [njet,njet,njet,(hE.iteratedFDeriv ℝ _).eq_of_nhds, iteratedFDeriv_add_apply ( (show ContDiffAt ℝ ω Z (L 0) from (L.map_zero.symm ▸ hu)).comp _ L.contDiff.contDiffAt|>.of_le le_top) ((show ContDiffAt ℝ ω D (Y' 0) from Y'.map_zero.symm ▸ hx).comp _ Y'.contDiff.contDiffAt|>.of_le le_top),_root_.add_apply, jets_linear L (hu.of_le le_top), jets_linear Y' (hx.of_le le_top) ]; simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]; rw [show ∀ {M N:Type} (p:M→N)(t:M), (fun i:Fin 2=>p (![t,t] i))=![p t,p t] from fun p x=> funext fun i=>by fin_cases i<;>rfl] -- both separately
      rw [show (fun i:Fin 2=> Y' (![x,x] i))=![Y' x,Y' x] from funext fun i=>by fin_cases i <;> rfl,show iteratedFDeriv ℝ 2 D 0=_ from iteratedFDeriv_const_smul_apply (hz.of_le le_top) (a:=(4:ℝ)⁻¹),_root_.smul_apply, smul_eq_mul]; change (iteratedFDeriv ℝ 2 Z 0 _+(4:ℝ)⁻¹*iteratedFDeriv ℝ 2 (taxY X! P) 0 _)/2= _+ iteratedFDeriv ℝ 2 (taxY X! P) 0 ![Y' x,Y' x]/2 /4; unfold L Z;ring
end YM.OPE.Cascade.Rill
