import YM.RegulatorIR.Binding.Landscape

/-! Only scale-ordered formal Taylor e in this local Laplace reader. M.agenda
parameter scalar; first-order through all finite e, no coupling strip. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Tree Tree.Forest Series Series.Radial
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}

-- common coupling t log-links. factor multiplies cost in exp(-β cost/t²).
structure Scale where
 beta : ℝ→ℝ
 stable : beta 0=1
 near : ContDiffAt ℝ ∞ beta 0
 measured : Measurable beta
 forward t : 0≤ beta t
-- for compatibility with formal Wilson reset with g_i=t γ_i(t)
def creator (α:ℝ→ ℝ) (h:Measurable α)(ht:ContDiffAt ℝ ∞ α 0)(he:α 0=1): Scale:=
 { beta:=fun z=>(α z)⁻¹^2, stable:=by simp [he], near:=(((ht.inv (show α 0≠0 by rw [he];exact one_ne_zero)).pow _)), measured:=h.inv.pow_const _,forward:=fun _=>sq_nonneg _ }
namespace Scale
variable (S:Scale)
lemma tend : Tendsto S.beta (𝓝 0) (𝓝 1):= S.stable ▸ S.near.continuousAt
lemma route (x:ℝ): Tendsto (fun t:ℝ=>S.beta (t*x)) (𝓝[≠] (0:ℝ)) (𝓝 1):= S.tend.comp (by simpa using (tendsto_id (x:=(𝓝 0))).mul_const x |>.mono_left nhdsWithin_le_nhds)
end Scale

variable (N:Scale)
def startO (N:Scale) : Hook G Empty (OEdge f):=fun t u _=>N.beta t*valueO u
lemma start_ray (x:Meadow G Empty × ℝ × Horizon G f): Tendsto (fees (priceMap (startO N)) · x) (𝓝[≠] (0:ℝ)) (𝓝 (costO x.2.2)):=by
 have ht:= (N.route x.2.1).mul (CostC x.2.2)
 rw [one_mul] at ht
 convert ht using 1;ext1 r; change _*_ /_=_; rw [mul_div_assoc]; rfl
lemma startF : Stationary (priceMap ((startO N):Hook G Empty (OEdge f))) := by
 apply declares
 · have hx:= (valueSmooth (f:=f) (G:=G))
   apply ContDiffAt.mul (N.near.comp (f:=fun x:Meadow G Empty × ℝ × Horizon G f =>(x.2.1:ℝ)) _ (contDiffAt_fst.comp (f:=Prod.snd) _ contDiffAt_snd))
   exact (hx.of_le le_top).comp (f:=fun x:Meadow G Empty × ℝ × Horizon G f=>x.2.2) (0:Meadow G Empty × ℝ × Horizon G f) (contDiffAt_snd.comp (f:=Prod.snd) _ contDiffAt_snd)
 exact fun x=>⟨_, start_ray N x⟩
lemma start_color (x:Meadow G Empty × ℝ × Horizon G f) : jet (priceMap (startO N)) 2 x=costO x.2.2:= tendsto_nhds_unique (due _ (startF N) x) (start_ray N x)
lemma value_cont : Continuous (valueO (G:=G) (f:=f)):= (energy_cont.comp (lift_cont G)).div_const _
lemma start (he:Even f.val): Stead (full G f) (startO N):=by
 refine ⟨?_,fun _ _ _=>mul_nonneg (N.forward _) (div_nonneg (energy_nonneg _) (by norm_num)),startF N,?_,?_⟩
 · exact Measurable.mul (N.measured.comp measurable_fst) (value_cont.measurable.comp (measurable_fst.comp measurable_snd))
 · intro r x u X W hr hx _ hm
   have h:= (N.tend.comp hr).mul ((value_cont.tendsto X).comp hx)
   have hh := tendsto_nhds_unique h hm; rw [one_mul] at hh
   exact ⟨End.goat_flat X he ((div_eq_zero_iff.mp hh).resolve_right (by norm_num)),fun _=> Subsingleton.elim ..⟩
 intro z; rw [start_color]
 exact ⟨costO_pos _,fun hh=>⟨costO_null _ he hh,fun _=>Subsingleton.elim ..⟩⟩

variable (S:StepData c f)(H:S.patch.Branches S.kernel G) {F:Forest S.ratio}
variable (V: Geometry.Field.Square F)
-- actual Forest interpolation

def dropQ (S:StepData c f)(F:Forest S.ratio)(G:Gauge): Transfer (OEdge f) (Wind F) G:= {
 inlet:= cloth F, curve:= injectX F, invariant:= chart_commute F, continuous:=cloth_cont F }

def nextO (F:Forest S.ratio)(N:Scale) : Hook G (Wind F) (OEdge c):=fun t b x=>N.beta t*bond S (cloth F x) b

include H
lemma next_ray (x:Meadow G (Wind F) × ℝ × Horizon G c) : Tendsto (fees (priceMap (nextO S F N)) · x) (𝓝[≠] (0:ℝ)) (𝓝 (feeO S (injectX F x.1) x.2.2)):=by
 have ht:= (N.route x.2.1).mul (smoke S H (injectX F x.1) x.2.2)
 rw [one_mul] at ht
 convert ht using 1;ext1 r; change (_*bond S (cloth F (expLinks _ _ (r • x.1))) _)/_= _; rw [chart_commute,map_smul,mul_div_assoc]; rfl
lemma nextF : Stationary (priceMap (G:=G) (nextO S F N)):=by
 let Z:= Meadow G (Wind F) × ℝ × Horizon G c
 have hp : priceMap (G:=G) (nextO S F N)= (fun x:Meadow G (Wind F) × ℝ × Horizon G c=> N.beta x.2.1*burn S (injectX F x.1) x.2.2):=by ext1 z; unfold priceMap nextO burn; rw [chart_commute]
 refine declares _ ?_ (fun x=> ⟨_,next_ray N S H x⟩)
 rw [hp]; let f: Z→ (Horizon G _)× (Horizon G c):=fun x=>(injectX (G:=G) F x.1,x.2.2)
 apply ContDiffAt.mul (N.near.comp (f:=fun x => (x.2.1:ℝ)) (0:Meadow G (Wind F) × ℝ × Horizon G c) (contDiffAt_fst.comp (f:=Prod.snd) _ contDiffAt_snd))
 have hz: f 0=(0,0):= Prod.ext (show (f 0).1=0 from (injectX F).map_zero) rfl
 refine (((show ContDiffAt ℝ ω (fun z: Horizon G _ × Horizon G c=>burn S z.1 z.2) (f 0) from hz.symm ▸ burn_smooth S H).comp (f:=f) _ ?_).of_le le_top)
 exact ContDiffAt.prodMk (((injectX F).toContinuousLinearMap.contDiff).contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst) (contDiffAt_snd.comp (f:=Prod.snd) _ contDiffAt_snd)
lemma next_color (z:Meadow G (Wind F) × ℝ × Horizon G c): jet (priceMap (nextO S F N)) 2 z= feeO S (injectX F z.1) z.2.2:= tendsto_nhds_unique (due _ (nextF N S H) z) (next_ray N S H z)
include V
lemma cross (he:Even c.val)(hf:Even f.val): Move (full G f) (full G c) (dropQ S F G) (nextO S F N):=by
 refine ⟨?_,fun _ _ _=>mul_nonneg (N.forward _) (bond_nonneg ..),nextF N S H,?_,?_⟩
 · apply Measurable.mul (N.measured.comp measurable_fst)
   let g:ℝ × RoomK G (OEdge c) × RoomK G (Wind F) → spins G f × spins G c:= fun x=>(cloth F x.2.2,x.2.1)
    --
   change Measurable ((fun x:spins G f × spins G c=> bond S x.1 x.2) ∘ g)
   exact (bond_meas S H).comp (show Measurable g from ((cloth_cont F (G:=G)).measurable.comp (measurable_snd.comp measurable_snd)).prodMk (measurable_fst.comp measurable_snd))
 · intro r x y X Y hr hx hy hu hv
   obtain ⟨k,hk,hK⟩:= hv
   have hp:=(N.tend.comp hr).mul ((flat_glow S H k hk (cloth F Y) hK X).tendsto.comp ((((cloth_cont F).tendsto _).comp hy).prodMk_nhds hx))
   have h:= tendsto_nhds_unique (b:=0) hp hu; change 1*bond S _ _=0 at h; rw [one_mul] at h
   have hY:= (bond_zero S (cloth F Y) X).mp h
   refine ⟨hY.symm ▸ glide S H _ ⟨k,hk,hK⟩,fun hX=> fiber_flat S H V _ ⟨k,hk,hK⟩ (hY.symm.trans hX)⟩
 intro z; rw [next_color N S H]
 refine ⟨feeO_nonneg ..,fun hq hh=> ?_⟩; have hv:= feeO_eq S _ _ hq
 exact ⟨hv.symm ▸ gradie_zone S H hh,fun hx=>fiber_core (S:=S) H (Q:=V) z.1 hh hf he (hv.symm.trans hx)⟩
end YM.RegulatorIR.Binding

namespace YM.RegulatorIR.Binding.Last
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Series Series.Radial
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {f:Side}
def shoot (f:Side)(G:Gauge) : Transfer (OEdge f) (Cotree f) G:= ⟨splitLink 1, inhabit, boots, tone G f⟩
lemma zeroStationary : Stationary (priceMap (0:Hook G (Cotree f) Empty)):= by
 refine declares _ (contDiffAt_const (c:=(0:ℝ))) (fun x=> ⟨0,?_⟩); change Tendsto (fun t:ℝ=>(0:ℝ)/t^2) _ _; simp
lemma zeroJet (z:Meadow G (Cotree f) × ℝ × Meadow G Empty): jet (priceMap (0:Hook G (Cotree f) Empty)) 2 z=0:= by
 apply tendsto_nhds_unique (due _ zeroStationary z); simp [fees,priceMap]
lemma carries (h:Even f.val): Move (full G f) (door G) (shoot f G) 0 := ⟨measurable_const,fun _ _ _=>le_rfl, zeroStationary,fun _ _ _ _ Y _ _ _ _ he=>⟨trivial,fun _=> settle Y h he⟩, fun z=>⟨(zeroJet z).ge,fun _ he=> ⟨trivial,fun _=>still _ h he⟩⟩⟩
end YM.RegulatorIR.Binding.Last
