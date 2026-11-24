import YM.Contacts.Junction.Prairie
/-! # diagnostic planting corrected model with arbitrary stencil costs, before chart transport. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (P : ChartRatio G) {Λ σ C e a v b d t K:ℝ}{n k j r:ℕ}
namespace Buyer
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom
variable (k) (B : BudgetPoint)(F:bore G)(p:Clip)(T:PathData G)
abbrev book (i:ℕ) : Trio.Offer G f:= pass (Province.slice k B.B T F p i) f
local notation "Y" => Link G f
local notation "α" => cap G f
local notation "S₀" => book (f:=f) k B F p T
local notation "Yp" => input G f
def biomass : α→ℝ:= stake (fun i=> plays (S₀ i)) (k+1)
def lit (i:ℕ) : Y→ℝ:= (Model.base p T f i ∘ Yp)+ plays (S₀ i)
def deficit (i:ℕ): Link G f→ℝ:= wind (hair F f) (k+3) i -lit k B F p T i
def debt (i:ℕ): Y→ℝ:= skel (deficit k B F p T i) (k+3-i)
def boom : α→ℝ := stake (debt k B F p T) (k+1)
def trib : α→ℝ:= biomass k B F p T+boom k B F p T
local notation "L" => lit k B F p T (f:=f)
local notation "Z" => deficit k B F p T (f:=f)
local notation "W" => biomass k B F p T (f:=f)
local notation "δ" => boom k B F p T (f:=f)
local notation "Ξ" => hair F f
variable {k B F p T}
variable (hp:T.Bounds p σ C Λ)(hx:∀ i≤k,Charted G k K B T F p d v a i n)(hk:2≤k)
variable {X:G.ColorIndex}{A:Bed}(hg:G.Simple) (hE:Aegis X F A) {f': ℝ → Config G f→ℝ}
    (he:Package f' (hair F f) (k+3)) (hb:Package (material p T) (hair F f) 5)
include hx
lemma candle (ht:j≤k) : AnalyticAt ℝ (plays (S₀ j)) 0:= by
   unfold plays Function.comp Trio.froth; exact ContDiffAt.analyticAt (ContDiffAt.sum fun i _=>((hx j ht).hull _ i).1.contDiffAt) -- prod x real
lemma eval_meas (ht:j≤k) : Measurable (Trio.froth (S₀ j)):= Finset.measurable_fun_sum _ fun x _=>(hx j ht).sector f x|>.borel
lemma measure_port  : Measurable W:= by
   let Q:=range (k+1); let F(i:ℕ):= plays (S₀ i); exact Finset.measurable_fun_sum Q fun i hi=> (measurable_fst.pow_const (i:ℕ)).mul (((eval_meas (j:=i) hx (f:=f) (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).comp (input_cont (G:=G)).measurable).comp measurable_snd) -- Fs unwrap
include hp
lemma highT (ht:j≤k) : AnalyticAt ℝ (L j) 0:= (armor_apt p T hp j).add (candle hx (f:=f) ht)
omit hp in
lemma loomT  : AnalyticAt ℝ W 0:= stake_ana fun j hj=> candle hx (f:=f) (by omega)
include hg hE hk
omit hp hx in
lemma rawT  : swell (hair F f) (k+3)= stake (wind (hair F f) (k+3)) (k+1):= by
   funext z; unfold swell stake; symm; refine Finset.sum_subset (Finset.range_mono (by omega : k+1≤k+3)) (fun i hi he=> ?_);
   unfold conjunct; apply mul_eq_zero.mpr; right; have hz(v:ℕ)(hv:v<k+3-i):= Plata.hair_quiet hE f hg (i+v-2) v (show v<2 from by have ht:= Finset.mem_range.mp hi; simp only [Finset.mem_range] at he; omega); apply Finset.sum_eq_zero (fun j hj=> ?_); unfold grate; split; rw [hz j (Finset.mem_range.mp hj),Forge.parcel_nil]; rfl
omit hx hp hE hg in
lemma rear (B:PathData G)(m:Side)(p:Clip) : enact (material (f:=m) p B)=stake (fun i=>Model.base p B m i ∘ input G m) (k+1):= by
     ext1 z; unfold stake; have hh i (x:cap G m): conjunct (Model.base p B m i ∘ input G m) i x= (if i=0 then mainTerm p B (input G m x.2) else 0)+ (if i=2 then x.1^2* Precision.loop B (input G m x.2) else 0):= by unfold conjunct Model.base; split_ifs <;> simp_all [Function.comp_apply];
     simp_rw [hh,sum_add_distrib]; simp [enact,material,show 2<k+1 from by omega]
omit hg hE in
lemma soma : enact (f:=f) (material p T)+W= stake (L) (k+1) := by rw [rear hk T f p]; unfold biomass stake; ext x; unfold lit; simp [Pi.add_apply,Ion.conjunct,mul_add,sum_add_distrib]
lemma bounty (hs:10*B.B<f.val) (hl:j≤k)(hu:r+j<k+3) (x:Y):
      ‖jet (Z j) r x‖ ≤ Fintype.card (Site f)*K^(-d)*‖x‖^r:= by unfold deficit; rw [jet_minus _ _ _ _ (wind_ana ..) (highT hp hx (f:=f) hl),norm_sub_rev,wind_jet,if_pos hu]; exact (hx j hl).precise _ hs _ _ hu
lemma asset  : AnalyticAt ℝ (swell (hair F f) (k+3)-(enact (material p T)+W+δ)) 0 ∧ Rays (k+3) (swell (hair F f) (k+3)-(enact (material p T)+W+δ)):= by
    let P(i:ℕ):= (Z i) - debt k B F p T i; let X(i:ℕ):= wind (hair F f) (k+3) i; rw [soma hp hx hk,rawT hk hg hE (f:=f)]; rw [show stake X (k+1) - (stake L (k+1) + δ)=stake P (k+1) from ?_]; swap; · ext x; unfold stake boom P X deficit; simp only [Pi.sub_apply,Pi.add_apply, stake, conjunct, Finset.sum_sub_distrib,mul_sub]; abel
    have h i (hi:i<k+1) : AnalyticAt ℝ (Z i) 0:= (wind_ana ..).sub (highT hp hx (f:=f) (by omega)); have he i (hi:i<k+1): AnalyticAt ℝ (P i) 0:= (h i hi).sub (Loom.skel_analytic ..); exact ⟨stake_ana he, Ion.good_spaces he fun i hi=>Loom.cords _ _ (h i hi)⟩
omit hg hE hp in
lemma boonT : AnalyticAt ℝ W 0 ∧ Rays 3 W:= by
     refine ⟨(loomT hx (f:=f)),good_spaces (hp:=fun i hi=>candle (j:=i) hx (f:=f) (by omega)) (fun i hi=>?_ )⟩; have hz:= Nat.le_of_lt_succ hi; refine (jet_bridge (candle (j:=i) hx (f:=f) hz)).2 fun x j hj=>?_ ; -- syntax
     unfold plays Trio.froth Function.comp; let a:= S₀ i; dsimp only; let f' y:= (a y ∘ input G f); change jet (fun x=> ∑ y,f' y x) j x=0; rw [loan_sum _ (F:=f') (fun y _=> ((hx i hz).hull _ y).1)]; exact sum_eq_zero fun y _=>(hx i hz).order _ y x _ (by unfold hero; omega)
include he hb
lemma hands : let y:= enact f'-enact (material p T); let Z₁:= trib k B F p T; Rays 3 Z₁ ∧ Rays (k+3) (y-Z₁):= by
   intro y z; let Q:= swell Ξ (k+3); let P:=enact (f:=f) (material p T); have hh : Rays (k+3) (y-z):= by
        rw [show y-z=(enact f'-Q)+(Q-(P+W+δ)) from (by unfold y z P trib; abel)]; exact he.exact.add (asset hp hx hk hg hE (f:=f)).2
   -- epochS param T issue T Tube! use reduce n absent. custom
   have hu:Rays 3 y:= by apply Milling.benchPitch (he.vest.sub hb.vest); intro x i hi; change jet (enact f'-P) i _=0; rw [jet_minus _ _ _ _ he.vest hb.vest,nightwalk (f:=enact f') he.vest (orchestra ..) he.exact _ (by omega) _,nightwalk (f:=P) hb.vest (orchestra ..) hb.exact _ (by omega) _,swell_front Ξ (k+3),swell_front Ξ 5,if_pos (by omega),if_pos (by omega),sub_self]
   exact ⟨by rw [show z=y-(y-z) from (by abel)]; exact hu.sub (hh.weaker (by omega)),hh⟩
omit he hb hg hp hE hk
lemma tribX : AnalyticAt ℝ δ 0∧Measurable δ∧Measurable (trib k B F p T (f:=f)):= by
    have he(i:ℕ):Continuous (debt k B F p T i (f:=f)):= continuous_iff_continuousAt.mpr fun i=> (Loom.skel_analytic ..).continuousAt; have hx': Measurable δ:= Finset.measurable_fun_sum (range (k+1)) fun i _=> (measurable_fst.pow_const (i:ℕ)).mul ((he i).measurable.comp measurable_snd); exact ⟨stake_ana fun i _=>Loom.skel_analytic ..,hx',(measure_port hx (f:=f)).add hx'⟩
end Buyer
end YM.Contacts.Junction
