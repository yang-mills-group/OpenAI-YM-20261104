import YM.LocalTaylorR2.Exponent.Bus
import YM.LocalTaylorR2.Kiln.Woven

/-!
 # Common analytics: full-unprofiled oscillators in the sensitive windows. No change to Cleanroom/podium when pulling.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
variable {X:Coat T F} {U:Support c}
section motion
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E] {U':E→ Config G c} {X' : E} {u:E→Directions G f}{z:E→Air f G}{w:Air f G}
lemma chording (X:Coat T F)(η:ℝ)(i:Bond f) (p:Glass P X U' X' j W)(h:Room P S T X.x)(he:Canary G A d)(hy:0<η)(Z:Support c)(hz:i∈edgesM S Z X.B):
    let f' v (s:F.Slice G×Air f G):= worldZ (vary (X.wrapY s.1) (U' v)) η (course (X.wrapY s.1) A η s.2 (U' v)); Drifts (towerScale S Z X.B F) (fun s v=> f' v s i) X' j:=by
 intro f'
 let z := towerScale (G:=G) S Z X.B F; have hP : ∀ i,1≤ z i:= towerMax Z X.B; let I:= edgesM S Z X.B; let Y:=lensS I G
 let f (t:F.Slice G×Air _ G):= swim Y t.2; let w (t:F.Slice G×Air _ G) v:= course (X.wrapY t.1) A η t.2 (U' v)
 have hy' : Drifts z (fun t (_:E)=>f t) X' j:= by
   refine ⟨1,zero_le_one,1,Eventually.of_forall fun y t=> (Brush.certified zero_le_one _).climb ?_ le_rfl⟩; rw [pow_one,one_mul]; unfold z towerScale f Y I; rw [chargedU]; linarith
 have hh : Drifts z (fun s v=> Pond.swim Y (w s v)) X' j:= (Drifts.more hP (Drifts.fat (p.towers (U:=fun i:F.Slice G × Air _ _=> i.2) (Y:=Prod.fst) h he I hy).2) hy').join (Eventually.of_forall fun _ _=> sub_add_cancel ..)
 let L:= gStep η • (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:↥I=> G.Color) (⟨i,hz⟩:↥I)).comp (stereo I G).toContinuousLinearMap
 exact Drifts.more hP (Drifts.fat ((p.settles (Y:=Prod.fst) h).replay (ContinuousLinearMap.proj i))) (hh.scaled L)
lemma ranges {Z:Support c} (i:Bond f)(he:i∈edgesM S Z X.B)(hm:Cash W X.x μ L Q o C T R) (hp:X.manifest)(hh:X.width=o.K) (hv:Clutch X w o.a R.beta y X' j U' u z) :
    let f' := facescale (edgesM S Z X.B) w; let M := y+o.cap*X.t+2*Fintype.card G.ColorIndex
    Brush j (M*f') 1 (fun x=> u x i) X':=by
  intro f' M; have ht : 0<X.t:= hm.laws.data.room.fiery; obtain ⟨h₀,_,_,h⟩:= hm.laws.data.safety
  let P:= worldZ X R.beta w i; have hx:1 ≤ f':= (Flux.expenses ..).1
  let I:=hm.laws.intake; have hβ : 1/2 ≤ R.beta := le_trans (by linarith [I.height]) I.window.1
  have hY:= hv.price; have hf:=Flux.expenses (edgesM S Z X.B) w
  let g:= gStep R.beta; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr I.positive); have hh' : g ≤ 2:= by
     unfold g gStep; rw [← one_div]; apply (div_le_iff₀ (Real.sqrt_pos.mpr I.positive)).mpr; nlinarith [Real.sq_sqrt I.positive.le,Real.sqrt_nonneg R.beta]
  have hZ := color_cover (A:=f') (zero_le_one.trans hx) (X.atmos w i) (fun j=> hf.2.2.2 (i,j) (mem_product.mpr ⟨he, mem_univ _⟩)) -- name?
  have hP : ‖u X' i‖≤o.cap*X.t + 2*(Fintype.card G.ColorIndex*f') := by
    rw [hv.base0 hm.laws.data.room hp]; apply (norm_add_le _ (g • X.atmos w i)).trans; rw [norm_smul,Real.norm_of_nonneg hg.le]; exact add_le_add ((h F X rfl hh hp).1 i) (mul_le_mul hh' hZ (norm_nonneg _) (by positivity))
  apply (hv.budded _ hP).climb _ le_rfl; unfold M; have h :0≤ y+o.cap*X.t:=by positivity
  nlinarith only [le_mul_of_one_le_right h hx]
lemma smallG (A:Support c) (hm:Cash W X.x μ L Q o C T R) (hp:X.manifest)(hh:X.width=o.K)(hv:Clutch X w o.a R.beta y X' j U' u z)(hz:w∉eerie X A (o.ξ/2) R.beta):
   ∀ᶠ y in 𝓝 X', ∀ i:Bond f, atEdge S i∈A → X.cone (2*o.a) (u y) i=1:=by
  apply eventually_all.mpr; intro i; by_cases he:atEdge S i∈ A; swap; · exact Eventually.of_forall fun _ hx=> (he hx).elim
  obtain ⟨ho,hℓ,hι,hZ⟩:= hm.laws.data.safety
  let B v:= ‖u v i‖; have hM:=o.large; have ht:0<X.t:=hm.laws.data.room.fiery
  have hV : B X'< 2*o.a*X.t := by
    unfold B; rw [hv.base0 hm.laws.data.room hp]; exact ((X.watch_bonds _ ht (half_pos o.rare).le hm.laws.intake.positive (atHome X _ _ _ _ hz _ he) i (by simp) ((hZ F X rfl hh hp).1 i)).2).trans_lt ((mul_lt_mul_of_pos_right (by nlinarith only [hℓ,hι,hM]) ht))
  filter_upwards [((hv.budded i le_rfl).smooth.continuousAt).norm.eventually (gt_mem_nhds hV)] with v hq _ using X.premiere (by positivity) _ i hq.le
-- eventual actual Healthy in stencil-facing Trans!!! on inside; use Clutch.darling: Pane stable then all agrees inspected.
lemma upperShape (a:ℝ)(C:ℝ)(g:ℝ)(p j:ℕ)(h:1≤C)(ha:0≤a)(hg:1≤g): stamp j p a (C*g) ≤ a*(stamp j p 1 C*g^(p+j)):=by
  unfold stamp; rw [Finset.sum_mul,Finset.mul_sum]; apply Finset.sum_le_sum; intro i hi; calc
    _ = a*((j.factorial*(crown j i*1*C^i)*(3*C)^j)*g^(i+j)):=by ring
    _ ≤ _:=by have hh:= crown_pos (k:=i) (j:=j); have h:=Nat.le_of_lt_succ (mem_range.mp hi); gcongr
lemma rateStamp (j p:ℕ) {K:ℝ→ℝ} (h:Rate G L 0 K): Rate G L 0 fun x=> stamp j p 1 (K x):= by
  unfold stamp
  generalize Finset.range (p+1)=s; induction s using Finset.induction_on with
  | empty=> simp_rw [sum_empty]; exact Rate.const _
  | insert i s h₀ ih=> simp_rw [sum_insert h₀]; apply Rate.add _ ih; simpa only [zero_add,zero_mul] using (((h.pow i).mul_left (crown j i*1)).mul_left (j.factorial:ℝ)).mul ((h.mul_left 3).pow j)
end motion
end YM.LocalTaylorR2.Exponent
