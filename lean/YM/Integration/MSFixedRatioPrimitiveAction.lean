import YM.FormalBulk08.Reef.Mouth
import YM.FVAAlt2.Booth.Tag

/-! The complete finite physical Haar and block-penalty primitives of
the two signed position programs on the original finite forest chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioPrimitiveAction
open Lattice RG Exterior Tree Stationary Precision Filter FormalBulk08 FormalBulk08.Jets
open RegulatorIR RegulatorIR.Prim RegulatorIR.Halo RegulatorIR.Geometry
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth RegulatorIR.FVAAlt2.Booth.Tape PertExtension
open PowerSeries RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Binding
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)

/-- The native pointwise Haar density in the regulator agrees locally
with the independent action chart with its original normalization. -/
theorem entry (O : ChartRatio G) (hO : LocalRatio O) :
    Prim.entry G =ᶠ[𝓝 0] fun x=>Real.log (O.J x) := by
  let J:=Orb.tray G
  let H:=Orb.traySpec G
  have hz : J.J=ᶠ[𝓝 0] O.J := (MS.Bare.Maurer.real_ratio (G:=G) H).trans (MS.Bare.Maurer.real_ratio hO).symm
  have hp : ∀ᶠ x in 𝓝 (0:G.Color),0<J.J x := (H.germ 0 (Metric.mem_ball_self H.patch)).continuousAt.eventually
    (lt_mem_nhds (show 0<J.J 0 from H.anchored.symm ▸ zero_lt_one))
  filter_upwards [Prim.genuine G,hz,hp] with x hg he hx
  rw [hg]
  unfold Prim.ent
  change Real.log (Chart.fee J x/Chart.fee J 0)=Real.log (O.J x)
  rw [←he]
  unfold Chart.fee
  rw [H.anchored,max_eq_left (mul_nonneg H.scale.le hx.le),mul_one,max_eq_left H.scale.le,
    mul_div_cancel_left₀ _ H.scale.ne']

variable (L : Binding.Scale) (a : Jets.Rays (Reef.Pine G S F⊕Reef.wire G c))
def fields (S₀ : StepData c f) (F₀ : Forest S₀.ratio)
    (x : Jets.Rays (Reef.Pine G S₀ F₀ ⊕ Reef.wire G c)) : Work.F03.Logs G c f :=
  Reef.frail (G:=G) (c:=c) (f:=f) (Reef.graft (S:=S₀) (G:=G) F₀ x)
def coordinates (S₀ : StepData c f) (F₀ : Forest S₀.ratio)
    (x : Jets.Rays (Reef.Pine G S₀ F₀ ⊕ Reef.wire G c)) : KFoot G→ℝ :=
  Tape.announceT (G:=G) (c:=c) (f:=f) (fields S₀ F₀ x) ∘ Booth.joint G f c
theorem free (i : F.Free) : Exterior.collect G (fields (G:=G) S F a).2 i.val=(Reef.stand G F (a ∘ (Sum.inl : Reef.Pine G S F→Reef.Pine G S F⊕Reef.wire G c))) i :=
  PiLp.ext fun k=>Flat.bring_alive (G:=G) (S:=S) F (a ∘ Sum.inl) (Reef.knot (G:=G) (S:=S) F i k)

def measuredHaar (S₀ : StepData c f) (F₀ : Forest S₀.ratio) (L₀ : Binding.Scale)
    (x : Jets.Rays (Reef.Pine G S₀ F₀⊕Reef.wire G c)) (t : ℝ) : ℝ :=
  ∑i:Edge (Site f),Prim.flank (Prim.prism (G:=G) S₀ F₀ L₀ (Sum.inl (Booth.hop f i))) (coordinates (G:=G) S₀ F₀ x) t

theorem haar (sq : Geometry.Field.Square F) (O : ChartRatio G) (hO : LocalRatio O) :
    measuredHaar (G:=G) S F L a =ᶠ[𝓝 0] fun t=>Real.log (Reef.sap (G:=G) (S:=S) F O (t • (a ∘ Sum.inl))) := by
  let y:=Reef.stand G F (a ∘ (Sum.inl : Reef.Pine G S F→Reef.Pine G S F⊕Reef.wire G c))
  have hv (t : ℝ) : measuredHaar (G:=G) S F L a t=∑i:F.Free,Prim.entry G (t • y i) := by
    unfold measuredHaar coordinates
    simp_rw [Tape.savored S F L (fields (G:=G) S F a) sq]
    rw [←Fintype.sum_subtype_add_sum_subtype (fun i=>i∉F.trunks)
      (fun i=>if i∈F.trunks then 0 else Prim.entry G (t • Exterior.collect G (fields (G:=G) S F a).2 i))]
    rw [Finset.sum_eq_zero (f:=fun i:{e:Edge (Site f)// ¬ e∉F.trunks}=>
      if i.val∈F.trunks then 0 else Prim.entry G (t • Exterior.collect G (fields (G:=G) S F a).2 i.val)) ?_,add_zero]
    · apply Finset.sum_congr rfl
      intro i _
      rw [if_neg i.property,free S F a i]
    · intro i _
      rw [if_pos (Classical.not_not.mp i.property)]
  have hp : ∀ᶠ x in 𝓝 (0:G.Color),0<O.J x := (hO.germ 0 (Metric.mem_ball_self hO.patch)).continuousAt.eventually
    (lt_mem_nhds (show 0<O.J 0 from hO.anchored.symm ▸ zero_lt_one))
  have ht(i:F.Free) : Tendsto (fun t:ℝ=>t • y i) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun t:ℝ=>t • y i):=continuous_id.smul continuous_const
    simpa only [zero_smul] using hcont.tendsto (0:ℝ)
  filter_upwards [eventually_all.mpr fun i=>(ht i).eventually ((entry O hO).and hp)] with t h
  rw [hv]
  change ∑i:F.Free,Prim.entry G (t • y i)=Real.log (∏i:F.Free,O.J ((Reef.stand G F (t • (a ∘ Sum.inl))) i))
  rw [map_smul]
  change ∑i:F.Free,Prim.entry G (t • y i)=Real.log (∏i:F.Free,O.J (t • y i))
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun i _=>(h i).1
  · exact fun i _=>(h i).2.ne'

/-- The native finite blocking energy is evaluated at the very same
nonlinear Wilson prediction and the true fine/coarse field ray. -/
theorem penalty (H : S.patch.Branches S.kernel G) :
    ∑i:Edge (Site c),Prim.tale (Prim.flank (Prim.prism (G:=G) S F L (Sum.inr (Booth.hop c i))) (coordinates (G:=G) S F a))=
      Prim.tale (fun t=>L.beta t*Reef.clack (G:=G) S (Geometry.directive S) (Reef.graft (G:=G) (S:=S) F (t • a))) := by
  unfold coordinates
  rw [Tape.outcomesR S F L H (fields (G:=G) S F a)]
  apply congrArg Prim.tale
  funext t
  rw [Reef.graft_linear]
  have hc:Stationary.arm G c 1 ((t • Reef.graft (G:=G) (S:=S) F a) ∘ Sum.inr)=
      t • (fields (G:=G) S F a).1 :=
    (Stationary.arm G c 1).map_smul t ((Reef.graft (G:=G) (S:=S) F a) ∘ Sum.inr)
  have hf:Stationary.arm G f 1 ((t • Reef.graft (G:=G) (S:=S) F a) ∘ Sum.inl)=
      t • (fields (G:=G) S F a).2 :=
    (Stationary.arm G f 1).map_smul t ((Reef.graft (G:=G) (S:=S) F a) ∘ Sum.inl)
  unfold Reef.clack Reef.frail
  rw [hc,hf]

theorem haar_taylor (sq : Geometry.Field.Square F) (O : ChartRatio G) (hO : LocalRatio O) :
    ∑i:Edge (Site f),Prim.tale (Prim.flank (Prim.prism (G:=G) S F L (Sum.inl (Booth.hop f i))) (coordinates (G:=G) S F a)) =
      Prim.tale (fun t=>Real.log (Reef.sap (G:=G) (S:=S) F O (t • (a ∘ Sum.inl)))) := by
  rw [←Prim.tale_sum]
  · have hs : ContDiffAt ℝ ∞ (fun t:ℝ=>Reef.sap (G:=G) (S:=S) F O (t • (a ∘ Sum.inl))) 0 := by
      have h : ContDiffAt ℝ ∞ (Reef.sap (G:=G) (S:=S) F O) ((0:ℝ) • (a ∘ Sum.inl)) := by
        simpa only [zero_smul] using Reef.sap_smooth F O hO
      exact ContDiffAt.comp (g:=Reef.sap (G:=G) (S:=S) F O) (f:=fun t:ℝ=>t • (a ∘ Sum.inl))
        0 h (contDiffAt_id.smul contDiffAt_const)
    apply Prim.tale_eq (hs.log (by rw [zero_smul,Reef.sap_root F O hO]; norm_num))
    filter_upwards [haar S F L a sq O hO] with t h
    simpa only [measuredHaar,Finset.sum_apply] using h
  · exact fun i _=>(Prim.rooted (G:=G) S F _).some.smooth_v _

/-- The actual finite array charged by the original regulator has the
full signed Haar and blocking Taylor value on the independent
fixed-ratio field ray, at every positive perturbative order. -/
theorem evaluated {Z : Prim.Branchix→RegulatorIR.Diagram.Orders (Prim.KFoot G)}
    (hz : Prim.Sphere S F L Z) (sq : Geometry.Field.Square F) (H : S.patch.Branches S.kernel G)
    (O : ChartRatio G) (hO : LocalRatio O) (e : ℕ) (he : 0<e) :
    coeff e (flavor 2 (Tape.announceT (G:=G) (c:=c) (f:=f) (fields (G:=G) S F a)) (Booth.studied Z f c)) =
      coeff e (Prim.tale (fun t=>Real.log (Reef.sap (G:=G) (S:=S) F O (t • (a ∘ Sum.inl))))) -
      coeff (e+2) (Prim.tale (fun t=>L.beta t*Reef.clack (G:=G) S (Geometry.directive S) (Reef.graft (G:=G) (S:=S) F (t • a)))) := by
  rw [Booth.aced hz _ he,Fintype.sum_sum_type,←haar_taylor S F L a sq O hO,map_sum,
    ←penalty S F L a H,map_sum,sub_eq_add_neg,←Finset.sum_neg_distrib]
  exact congrArg₂ (fun x y:ℝ=>x+y) (Finset.sum_congr rfl (fun i _=>one_mul _))
    (Finset.sum_congr rfl (fun i _=>neg_one_mul _))

theorem purchased (sq : Geometry.Field.Square F) (H : S.patch.Branches S.kernel G)
    (O : ChartRatio G) (hO : LocalRatio O) (e : ℕ) (he : 0<e) :
    coeff e (flavor 2 (Tape.announceT (G:=G) (c:=c) (f:=f) (fields (G:=G) S F a)) (Booth.studied (Prim.gauss (G:=G) S F L H).choose f c)) =
      coeff e (Prim.tale (fun t=>Real.log (Reef.sap (G:=G) (S:=S) F O (t • (a ∘ Sum.inl))))) -
      coeff (e+2) (Prim.tale (fun t=>L.beta t*Reef.clack (G:=G) S (Geometry.directive S) (Reef.graft (G:=G) (S:=S) F (t • a)))) :=
  evaluated S F L a (Prim.gauss (G:=G) S F L H).choose_spec sq H O hO e he

end YM.Integration.MSFixedRatioPrimitiveAction
