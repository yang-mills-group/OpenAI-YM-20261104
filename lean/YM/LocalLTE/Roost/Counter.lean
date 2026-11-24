import YM.LocalLTE.Roost.Figs
/-! diagonal log and chair coarea.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r W s y η γ B : ℝ} {j n m : ℕ}
lemma freezeBase {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G)(j:ℕ)(hj:1≤j){p:ℝ→ℝ}{η a Q:ℝ} (h:Torch η a Q)(hW:W<0)(hp:Rate G L W p)(hh: ∀ᶠ x:ℝ in atTop,0≤p x):∃ V:ℝ→ℝ,Rate G L 0 V∧ ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → Works P L t S T→ ∀ (F:Forest S.ratio) (X:Coat T F), X.x=t → Allow X.blank.plate (along S) (tubularPrice G L) η a Q → ∀ x:Disk G c, ‖x‖≤p t → ∀ i:Bond f, Brush j (V t) 1 (fun y=> (timeΛ X y).undercurrent i) x:= by
  obtain ⟨A,e,q,Y,V,hA,hy,hZ,HR⟩:= lofty P L D hd j hj hW hp hh η a Q h
  let m:= tubularPrice G L; let C:ℝ:= (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η a Q m); let u x:= C+crownP j (radiusB x) m G e q A A
  let Z x:= V x + driftP j (V x)
  have hu : Rate G L 0 u:= (Rate.const _).add (((polynomial G L j m _ _).mul_left _).mul_left (Fintype.card G.ColorIndex))
  refine ⟨fun t=> |u t*(1+Z t)^j|, (by apply (show Rate G L 0 _ from ?_).compare (Eventually.of_forall fun x=> (abs_abs _).le); simpa only [zero_mul,zero_add] using! hu.mul (((Rate.const 1).add (hZ.add (hZ.mul_left j))).pow j)),?_⟩
  refine HR.mono fun t ht c f S T hS hP F X hx hκ x hy i=>?_ ; have hq: X.B=radiusB t:=congr_arg _ hx
  let K:=X.shutter; have hh : ‖Batch.joint X.blank.plate K i‖≤ C:= Batch.nearBase K h hκ i
  let f' (v: ZipP G c f):= (dry X v).undercurrent i; change Brush j _ _ (fun z=> f' (pass z)) x
  obtain ⟨ha,hb,h₁⟩:= ht c f S T hS hP F X hx hκ _ ((tally (f:=f) x).trans hy)
  simp_rw [sidefix]
  by_cases he:voyage X.blank.seeds (200*X.B) i
  · exact Brush.zi (Eventually.of_forall fun i=> if_pos he) (abs_nonneg _) zero_le_one
  have hz:= plotsB K (fun i=>(dry X i).plate) ha (hb.tilt le_rfl le_rfl (le_refl (0:ℝ)) hb.scale) hA.prices.le hA i
  have hg : Brush j (u t) (Z t) f' (sideways x):= by
    have hf : Brush j (C+crownP j X.B m G e q A A) _ f' (pass x):= (semi (((Brush.certified hz.pos (Batch.joint X.blank.plate K i)).climb hh le_rfl).separating hz)).shimmy (Eventually.of_forall fun _=> if_neg he)
    unfold u; rw [← hq]; exact hf
  apply ((Brush.reading sideways hg.trim norm_side)).climb (le_abs_self _) (by norm_num)

def solar (X:Coat T F)(z:Air f G)(Ñ:ChartRatio G)(b:Disk G c)(i:Bond f):= if i∉X.blank.plaza (X.blank.seeds.dome (304*X.B)) ∧ X.blank.Hot i then Real.log (Ñ.J (switchΛ X z b i)) else 0
lemma sunlit {P:Teller G}(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(D:Patch)(hd:D.Branches P.bind G){W:ℝ}(o: Target.Order G W)(j:ℕ)(hj:1≤j){p u:ℝ→ℝ}{v:ℝ}(h : -(1/2:ℝ)≤v)(hW:v<0)(hp:Rate G L v p)(hu:Rate G L 0 u)(hh: ∀ᶠ x:ℝ in atTop,0≤p x):∃ V:ℝ→ℝ,Rate G L 0 V∧ ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |u t|)→∀ x: Disk G c,‖x‖≤p t → ∀ i:Bond f,
   Brush j (V t) 1 (fun v=>solar X z Q.table v i) x:=by
  obtain ⟨A,C,hA,hC,H⟩:= glideGrowth L D hd Q W o j hj h hW hp hu hh
  let F:=fun y:G.Color=> Real.log (Q.table.J y); have hs:=Q.table_exists
  obtain ⟨M,hM,hH⟩:= Brush.neighborhood (k:=j) (0:G.Color) ((show ContDiffAt ℝ ω F 0 from (hs.germ 0 (mem_ball_self hs.patch)).log ((hs.pos 0 (mem_ball_self hs.patch)).ne')).of_le le_top)
  obtain ⟨r,hr,hX⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp hH
  have he:= hC.compare (v:=fun x=> |C x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  let p₀ t:= (j.factorial*M)*(1+(1+1*|C t|)*1)^j; refine ⟨p₀,?_,?_⟩
  · have hz:=Rate.const (G:=G) (L:=L) 1; simpa only [zero_mul] using! (((hz.add ((hz.add (he.mul_left 1)).mul_right 1)).pow j).mul_left (j.factorial*M))
  filter_upwards [H,hA.below hW _ hr] with t ht hh c f S T hS μ α Y F' X hx he z hz y hy i
  obtain ⟨hS,hq⟩:=ht c f S T hS _ _ Y F' X hx he z hz y hy
  unfold solar; split
  · let P : Directions G f→L[ℝ] G.Color:=ContinuousLinearMap.proj i; have hp : ‖P (switchΛ X z y)‖ ≤ r:= ((norm_le_pi_norm (switchΛ X z y) _).trans hS).trans hh
    exact ((hq.report P (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by rw [one_mul]; exact norm_le_pi_norm x _)).pine (hX (mem_closedBall_zero_iff.mpr hp))).trim
  exact (Brush.certified zero_le_one (0:ℝ)).climb (by unfold p₀; rw [norm_zero]; positivity) le_rfl
end YM.ConnectedActivityE6.Blaze.Vine
