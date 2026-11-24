import YM.FVA2.Vertices

/-!
# Calculate FP generator vertex in BV conventions

The matrix acting on the site Lie algebra, attached to ghost variables
(per actual period) with pulled-back fields, equals the FP determinant's
matrix. Analytic identities near flat propagator. All diagrams (including
tuning variations) must use this same normalization. Signs sensitive to `K`.
It uses **unmarked** action & sources separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.PairCoords
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Chart
open Function Filter Metric MeasureTheory TreeBasis Trans
open Wilson Based GaussianScore MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare MS.Plane MS.Landau MS.Koszul
open Modes MS.Native MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native.Draft MS.Native.Wilsonian MS.Native.Chart MS.Puff MS.Puff.Engine MS.Puff.Mom MS.Book MS.Book.Program MS.Bare.Focus Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {U J:Type} {n:Side}
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n)) [Fintype U][Fintype J]

set_option quotPrecheck false
local notation "K.atom" => Pos G n
local notation "Fκ" => Wilson.Field G n
local infixr:79 " ** " => product (φ (U:=U) (J:=J))
local notation "T" => LMap G n
local notation "Φ"=> plug (mkPlug m b)
local notation "ιc" => ink (bell (J:=J) m)

def onCity (x:Edge (Site n)) (a:G.ColorIndex)(j:J) : City G (Site n)→ℝ:=
     fun v=> (Chart.roam (drive n) v (ghostC b j) x) a

def vert (x:Edge (Site n)) (a:G.ColorIndex)(j:J) : Fκ→ℝ:= onCity b x a j ∘ LMap G n
abbrev localV (x:Edge (Site n))(a:G.ColorIndex)(t:Eyes G (Site n)) := projector (x,a) ∘ loco (drive n) t
omit [Fintype J] in
lemma ljets (x:Edge (Site n))(a:G.ColorIndex)(j:J) :
     onCity b x a j=∑ t:Eyes G (Site n), ghostC b j t.1 t.2 • localV x a t:= by
   let F:= ghostC b j; funext u; unfold onCity; nth_rw 1 [show ghostC b j= _ from (Native.frame F).symm]; rw [map_sum,Finset.sum_apply,Finset.sum_apply,WithLp.ofLp_sum,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [projector_k,map_smul,localV]; rfl
omit [Fintype J] in
lemma cleanV (x:Edge (Site n))(a:G.ColorIndex)(j:J): germ (vert b x a j):= by
   unfold vert; rw [ljets]; apply ContDiffAt.comp (f:=T) 0 _ (T).contDiff.contDiffAt; rw [map_zero]; -- sum rule
   have ht (t:Eyes G (Site n)): germ (localV x a t) := (projector (x,a)).contDiff.contDiffAt.comp _ (ride (drive n) t)
   let f:=fun (i:Eyes G (Site n))=> ghostC b j i.1 i.2 • localV x a i; change ContDiffAt ℝ ω (∑ i,f i) 0; rw [show ∑ i,f i=fun x=>∑ i,f i x from funext (fun x=> Finset.sum_apply x univ f)];  exact ContDiffAt.sum fun i _=> (ht i).const_smul (_:ℝ)
omit [Fintype U] [Fintype J] in
lemma cap_local (x:Edge (Site n))(a:G.ColorIndex)(j:J):
    ιc (vert b x a j)=∑ t:Eyes G (Site n),(ghostC b j t.1 t.2:ℂ) • ιc (localV x a t ∘ T):= by
   have ht t: germ (localV x a t ∘ T) := by apply ContDiffAt.comp 0 _ (T).contDiff.contDiffAt; rw [map_zero]; exact (projector (x,a)).contDiff.contDiffAt.comp _ (ride (drive n) t)
   rw [show vert b x a j=∑ t:Eyes G (Site n), ghostC b j t.1 t.2 • (localV x a t ∘ T) from funext (fun i=> by rw [vert,Function.comp_apply,ljets]; simp only [Finset.sum_apply]; rfl), ink_sum (F:=fun i=> ghostC b j i.1 i.2 • (localV x a i ∘ T)) _ _ (fun i _=> (ht i).const_smul (ghostC b j i.1 i.2))]; simp_rw [ink_smul _ (ht _)]

lemma to_steer (x:Edge (Site n))(i:G.ColorIndex):
   Φ ((throat (drive n) x i).val) =∑ j:J, atLetter (c j) ** ιc (vert b x i j):= by
   rw [throat_frame, Focus.launch_stone]; unfold Focus.stone; rw [map_sum]; simp_rw [cap_local,map_sum ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=>?_ ; change Φ (product σbranch (GH j.2 j.1).val (reads (localV x i j)))= _; have hv: germ (localV x i j):= (projector (x,i)).contDiff.contDiffAt.comp _ (ride (drive n) j);
   rw [plug_product _ (lawful m b), ghostPlug,pin_read m b hv,map_sum, LinearMap.sum_apply]; simp_rw [ map_smul,LinearMap.smul_apply ]

omit [Fintype U] [Fintype J] in
lemma forgetB (x:Site n)(a:G.ColorIndex): Φ ((GHplus a x).val)=0:=by apply atLetter_erase _ _ (x:=(Bfield a,x)); intro i; rcases i with i|⟨j|j⟩ <;> rfl

-- patched full sum not center-only
omit [Fintype U] [Fintype J] in
lemma ropes_only : Φ (sumHome (ropes G (drive n) 0)).val=
     ∑ i:Edge (Site n),∑ a:G.ColorIndex,Φ (AHplus a i).val ** (Φ (throat (drive n) i a).val):= by
   have he(t:Site n): Lab.Shift t (ropes G (drive n) 0)=ropes G (drive n) t:= by rw [show Lab.Shift t (ropes G (drive n) 0)= ropes G (drive n) (t+0) from sail_rope G (fun i : Site n=> t+i) (fun _ _=> (add_assoc ..).symm) 0]; simp
   rw [total_uses]; simp_rw [he]; simp only [ropes,sum_stack,Submodule.coe_sub,coupled,map_sum,map_sub,plug_product (mkPlug m b) (lawful m b), forgetB,map_zero,LinearMap.zero_apply,Finset.sum_const_zero,sub_zero, Fintype.sum_prod_type (α₁:=Site n) (α₂:=Axis)]

-- raw matrix entry convention bar-row j, c-col i
-- use via real QiAfter. cK wick from GrassSlice.
def bill (j i:J) : Fκ → ℝ:= fun x=> b.coord j (((plan G n).ghosts x) (b i))
omit [Fintype J] in
lemma bill_grown (j i:J) : germ (bill b j i):= by
   unfold bill SectionBasis.ghosts; change ContDiffAt ℝ ω (fun x=> b.coord j ((plan G n).projection ( TreeBasis.directed G (rim n) _ _))) 0
   let C:= ((b.coord j).comp ((plan G n).projection)).toContinuousLinearMap; let f(x: Wilson.Field G n):Cone G n:= TreeBasis.directed G (rim n) ((plan G n).L x) (b i)
   refine C.contDiff.contDiffAt.comp (f:=f) 0 (contDiffAt_pi.mpr ?_)
   intro t; let u:= ((guarded G (rim n)) (b i)); let w: Maurer.Ends G:=(u ((rim n).fromEdge t),u ((rim n).toEdge t)); let g:Fκ→G.Color:=fun v=> (plan G n).L v t
   have hg:g 0=0:= by unfold g; rw [map_zero]; rfl
   apply ContDiffAt.comp (g:=Maurer.volts w) (f:=g) _ _ ((contDiff_apply ℝ G.Color t).contDiffAt.comp _ (plan G n).L.toContinuousLinearMap.contDiff.contDiffAt); rw [hg]; exact Maurer.home _

lemma color_cook (p q:Param G n) (x:Cone G n) {s : Set G.El}{r:ℝ} (he:_root_.Even n.val) (H:LocalH.Geom G s (ball 0 r))(hS:∀ k,coverL G n x k∈ ball 0 r) : productCone G n (turn G (rim n) x (meanZero G n p)) (d G (rim n) q) =
  (∑ k:Edge (Site n),∑ a:G.ColorIndex, ((roam (drive n) (coverL G n x) (siteCover G n p) k) a)*coverL G n (d G (rim n) q) k a)/2:= by
     change (∑ i:Edge (Site n), Inner.inner ℝ _ _)/2=_; simp_rw [colour_cost,formal_cover G n he x H hS]; rfl

omit [Fintype J] in
lemma bill_near (he:_root_.Even n.val)(j i:J): (bill b j i)=ᶠ[𝓝 0]
       fun x=> -(∑ e:Edge (Site n),∑ a:G.ColorIndex, kField b j e a * vert b e a i x) / 2:= by
   obtain ⟨r,hr,hR⟩:=LocalH.geom_patch G; have hh: Tendsto T (𝓝 0) (𝓝 0):=by simpa using (T).continuous.tendsto 0
   filter_upwards [hh.eventually (Filter.eventually_all.mpr (fun i:Edge (Site n)=> ((continuous_apply i).tendsto (0: Lot G (Edge (Site n)))).eventually (Metric.ball_mem_nhds (0:G.Color) hr)))] with x hx
   have h:ℓ G n (dualB b j)=b.coord j:= (poisson G n).apply_symm_apply _
   rw [bill, mean_at G n he (b i) x (hR r (le_refl r)) hx,← h,ghost_turn,stream]; change productCone G n _ _=_; rw [color_cook _ _ _ he (hR r (le_refl r)) hx]; congr 1
   unfold kField vert; simp_rw [ ← Finset.sum_neg_distrib,Pi.neg_apply,PiLp.neg_apply,neg_mul,neg_neg]; unfold onCity; simp only [Function.comp_apply]; exact sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=>mul_comm ..
end YM.FVA2.PairCoords
