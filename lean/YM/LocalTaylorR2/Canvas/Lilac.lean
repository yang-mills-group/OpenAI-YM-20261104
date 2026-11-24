import YM.LocalTaylorR2.Canvas.Meridian
/-!
 # V animation on pricing set, meas. on all partners. Zest on
 pruned variables and still retaining real argument choice.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R:Rep G f}{X X':Coat T F}{b a γ W α y' ζ d q :ℝ}{χ:Chi}{j p' l :ℕ}
variable {w w':Air f G}{Z:Support c}{k k':Finset ℕ} {J : Basecamp G}
open Work.G05 Animals Itinerary
section meas
variable {E : Type} [MeasurableSpace E] {V' : E→ Config G c} {u : E → Directions G f} {Y : E→ F.Slice G}
-- Facility adapted
set_option maxHeartbeats 400000 in
lemma expose (J : Basecamp G)(_ht : ShellAccess S G X.x W X.width γ) (i:Coat.Stream c f) (he : Measurable V')(_hp:Measurable Y)(_hu:Measurable u) : Measurable fun x=> (arbor J (drive X (V' x) (Y x)) i (u x)).1 := by
  let Z x:= drive X (V' x) (Y x)
  let V x:= pull i.1 0 (V' x); let o := lead S i.2
  have hV:Measurable V:= (continuous_pull (G:=G) i.1 (0:Site c)).measurable.comp he
  have ha (i:Site c): Measurable (fun x=> carrier o (V x) i) := (continuous_travel (G:=G) (carriage o i) o).measurable.comp hV
  refine measurable_pi_lambda _ fun j=>?_
  change Measurable fun y=> point J X.χ (bed X) o (V y) j; unfold point; split_ifs
  · exact (J.log.borel X.χ).comp (((ha _).mul ((measurable_pi_apply j).comp hV)).mul (ha _).inv)
  exact measurable_const
set_option maxHeartbeats 400000 in
lemma hoist (ht : ShellAccess S G X.x W X.width γ)  (he : Measurable V')(hp:Measurable Y)(hu:Measurable u)  : Measurable fun x=> (drive X (V' x) (Y x)).signal (u x) :=by
  let Z x:= drive X (V' x) (Y x)
  have hf : Measurable fun x=> (Z x).saved := by
    apply measurable_pi_lambda; intro i
    change Measurable fun x=> if _∨X.Hot i then 0 else cutLog X.χ (X.width*X.t) (F.drape (Y x) i * (replica S.ratio (V' x) i)⁻¹)
    split_ifs
    · exact measurable_const
    exact (ht.log.borel X.χ).comp ((((measurable_pi_apply i).comp F.continuous_drape.measurable).comp hp).mul
      ((measurable_pi_apply i).comp (((Art.loyal (G:=G) (S:=S)).measurable).comp he)).inv)
  have hg : Measurable X.lens := by
    apply measurable_pi_lambda; intro i; unfold Coat.lens; split_ifs
    · exact measurable_pi_apply _
    exact measurable_const
  have hu': Measurable (fun x=> (Z x).signal (u x)):= hf.add (hg.comp hu)
  exact hu'
lemma mined {V':E→ Config G n}{Z:E→ Directions G n} (s:Signed) (j:Bond n)(he:Measurable V')(hu':Measurable Z): Measurable (fun x=>displacement s (Z x) (V' x) j):=by
  have hb {f:E→ G.Color}{g:E→ G.El}(hg:Measurable g)(hf:Measurable f):Measurable fun y=>G.adjoint (g y) (f y) := by
    change Measurable ((fun x:G.El×G.Color=> G.adjoint x.1 x.2) ∘ fun x=> (g x,f x))
    apply Measurable.comp (g:=fun x:G.El×G.Color=> G.adjoint x.1 x.2) (f:=fun x=>(g x,f x)) _ (hg.prodMk hf); exact (Art.optical G).measurable
  unfold displacement; dsimp only; have hh:= (measurable_pi_apply (edge s j)).comp hu'; split_ifs with hx
  · exact (hb (g:=fun y=> (V' y (edge s j))⁻¹) (((measurable_pi_apply _).comp he).inv) hh).neg
  exact hh
lemma expose' (J : Basecamp G)(ht : ShellAccess S G X.x W X.width γ) (i:Coat.Stream c f) (he : Measurable V')(hp:Measurable Y)(hu:Measurable u) : Measurable fun x=> (arbor J (drive X (V' x) (Y x)) i (u x)).2 := by
  let Z x:= drive X (V' x) (Y x)
  let V x:= pull i.1 0 (V' x); let o := lead S i.2
  have hV:Measurable V:= (continuous_pull (G:=G) i.1 (0:Site c)).measurable.comp he
  have ha (i:Site c): Measurable (fun x=> carrier o (V x) i) := (continuous_travel (G:=G) (carriage o i) o).measurable.comp hV
  have hb {f:E→ G.Color}{g:E→ G.El}(hg:Measurable g)(hf:Measurable f):Measurable fun y=>G.adjoint (g y) (f y) := by
    change Measurable ((fun x:G.El×G.Color=> G.adjoint x.1 x.2) ∘ fun x=> (g x,f x))
    apply Measurable.comp (g:=fun x:G.El×G.Color=> G.adjoint x.1 x.2) (f:=fun x=>(g x,f x)) _ (hg.prodMk hf); exact (Art.optical G).measurable
  refine measurable_pi_lambda _ fun j=>?_
  change Measurable fun x=> if distAt S j o≤ bed X then _ else 0; split_ifs
  · have hf : Measurable (fun x=> displacement i.1 ((Z x).signal (u x)) (replica S.ratio (V' x)) j):=by
      exact mined i.1 j ((Art.loyal (G:=G) (S:=S)).measurable.comp he) (hoist ht he hp hu)
    exact hb (ha _) hf
  exact measurable_const
lemma flow (J : Basecamp G)(ht : ShellAccess S G X.x W X.width γ) (i:Coat.Stream c f) (he : Measurable V')(hp:Measurable Y)(hu:Measurable u) : Measurable fun x=> arbor J (drive X (V' x) (Y x)) i (u x) := by
  unfold arbor; exact (expose J ht i he hp hu).prodMk (expose' J ht i he hp hu)
set_option maxHeartbeats 400000 in
lemma born (J : Basecamp G)(p : Room P S T X.x)(ht : ShellAccess S G X.x W X.width γ) (i:Coat.Stream c f) (he:Measurable V')(hp:Measurable Y){w:E→ Air f G} (hu:Measurable w): Measurable fun x=> pineCone J (drive X (V' x) (Y x)) a R i l (worldZ (drive X (V' x) (Y x)) R.beta (w x)):= by
  let Z x:= drive X (V' x) (Y x); let L x:= voltage (Z x); let a' x:=worldZ (Z x) R.beta (w x)
  obtain ⟨hL,-,hY⟩:=compassBro p.accepted he X hp ht R.beta; have hh:= hY w hu
  have hC : Measurable (fun t=> Vine.costs (Z t) (L t) i.1 i.2):= by
    refine Finset.measurable_fun_sum _ fun j _=> ?_; change Measurable fun v=> if X.selected _ _ then _ else 0; split_ifs
    · exact (((Shield.strains p.accepted he X hp ht hL i.1 j).norm.pow_const 2).div_const 2)
    exact measurable_const
  change Measurable fun t=> if Inside (rowSite S i) X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation * (X.enforce (2*a) (a' t) (X.booth (rowSite S i)) * blockTaylor l (ivy T X.x (choice i.1 X.k) i.2) (arbor J (Z t) i (a' t)) + Vine.costs (Z t) (L t) i.1 i.2); split_ifs
  · exact measurable_const
  exact measurable_const.mul ((((X.enforce_b (2*a) (X.booth _)).comp hh).mul ((blockTaylor_contDiff l (ivy T X.x (choice i.1 X.k) i.2) 0).continuous.measurable.comp (flow J ht i he hp hh))).add hC)
end meas

section zest
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → Config G c} {w:A→ E→ Directions G f} {Y: A→ F.Slice G} {x:E}
open Zest Glass
-- All courses on this symbol (not just over an inferred Interior by comparing V voltage at the same configurations outside legal Healthy).
lemma grove (h:Glass P X U x j W) (w:A→ E→ Directions G f)(hw: Zest w x j) (J:Basecamp G)(i:Coat.Stream c f): Zest (fun s v=> arbor J (drive X (U v) (Y s)) i (w s v)) x j:=by
  let V v:= pull i.1 0 (U v); let o:= lead S i.2; obtain ⟨v,hv⟩ := h.sails
  let Z s v:= drive X (U v) (Y s)
  refine Zest.pair ?_ ?_
  · refine single (f:=fun v=> point J X.χ (bed X) o (V v)) (contDiffAt_pi.mpr (fun j'=> ?_)); unfold point; split_ifs
    next he => exact J.smooth (beacon j v j' (separation o j'.1+1) le_rfl (Blaze.turn hv _)).smooth
    exact contDiffAt_const
  have hh : Zest (fun s v=> (Z s v).signal (w s v)) x j := by
    let D:Directions G f →ₗ[ℝ] Directions G f :=
      { toFun:= X.lens
        map_add' g u:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h]
        map_smul' q v:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h] }
    exact (h.weather.via Y).together (hw.replay D.toContinuousLinearMap)
  refine folds (f:=fun s v=> (arbor J (Z s v) i (w s v)).2) (fun p=>?_)
  change Zest (fun s v=> if distAt S p o ≤ bed X then _ else 0) x j; split_ifs
  · obtain ⟨C,hC,hY⟩:= (hh.replay (ContinuousLinearMap.proj (R:=ℝ) (edge i.1 p))).post -- parameter name?
    let u := v+1; have hu:u≥0:= add_nonneg hv.pos zero_le_one; let g:= royalty G; let z x:=carrier o (V x) (atEdge S p); let B:=(carriage o (atEdge S p)).length*(u*g); have hh':1≤g:=royalty_ge G
    have hb:0≤ B:=by unfold B; positivity
    refine ⟨ (g*(g*(C*g)*g))*(1+(B+(u+1+u)+B))^j, by positivity,?_⟩
    filter_upwards [hY,widen_mode hv (show v<u from lt_add_of_pos_right _ zero_lt_one)] with y hy hM s
    exact (decorate (g:=z) (tour (U:=V) (carriage o (atEdge S p)) o hu (Blaze.turn hM _).atLink) (Vine.displacement_pay i.1 p C 1 hM (hy s))).trim
  exact Zest.still _
lemma braced (J: Basecamp G)(p: Room P S T X.x)(h:Glass P X U x j W)(hp: Canary G b d)(hb:0<a*X.t)(he: 8*a*X.t ≤ b/2)(i:Coat.Stream c f)(hk:0<R.beta): Zest (fun (t:F.Slice G×Air f G) y=> let Y:=X.wrapY t.1; let V' := vary Y (U y); pineCone J V' a R i l (worldZ V' R.beta (course Y b R.beta t.2 (U y)))) x j:=by
  let X' (s:F.Slice G×Air f G):=X.wrapY s.1; let V (s:F.Slice G×Air f G) y:=drive X (U y) s.1 -- type
  let A s:=worldZ (X' s) R.beta s.2; let L s y:= steer (X' s) b (fun i=>prune b (A s i)) (U y); let O:=X.booth (rowSite S i)
  change Zest (fun t y=> if Inside _ X.seeds (200*X.B) then (0:ℝ) else (- R.beta*Raw.orientation)* _) x j; split_ifs
  · exact Zest.still _
  have hz : Zest L x j:= (h.foreshadow (Y:=Prod.fst) A hp).1
  let L' t y:= worldZ (V t y) R.beta (course (X' t) b R.beta t.2 (U y))
  have hv : Zest (fun s v=> Vine.costs (V s v) (voltage (V s v)) i.1 i.2) x j := by
    refine Zest.total _ _ (fun j' (_:j'∈parents i.2)=>?_); unfold Vine.pot; change
      Zest (fun t y=> if X.selected i.1 _ then ‖_‖^2 /2 else (0:ℝ)) x j
    split_ifs
    next ht=> exact (h.fellows _ p (Y:=Prod.fst) (i.1,j') ht (h.settles (Y:=Prod.fst) p)).wand (p:=fun y:G.Color=> ‖y‖^2/2)
                ((contDiff_norm_sq ℝ).div_const _)
    next h=> exact Zest.still _
  have hu : Zest (fun t y=> X.enforce (2*a) (L t y) O * rootTaylor J (V t y) i l (L t y)) x j:=
    (Zest.full _ _ (fun i' _ => (hz.replay (ContinuousLinearMap.proj i')).wand (Glass.tip (X:=X) _))).paint
      ((Canvas.grove (Y:=Prod.fst) h L hz J i).wand (p:=blockTaylor l (ivy T X.x (choice i.1 X.k) i.2)) (blockTaylor_contDiff ..))
  refine Zest.scalar (hf:= (Zest.congr hu (g:=fun t y=> X.enforce (2*a) (L' t y) O * rootTaylor J (V t y) i l (L' t y)) ?_).together hv) _
  refine Eventually.of_forall (fun y s=>?_)
  have hL : Transfer X _ (L s y) (4*a*X.t):= Transfer.mk (u:=L' s y) (by rw [show L' s y=steer (X' s) b (A s) (U y) from Silica.proceeds (X' s) _ hk s.2 (U y)]; intro i; exact (fruit (X' s) hp (U y) (A s) (show 4*a*X.t≤_ by nlinarith only [he,hp.warm])).both i)
  have hv j:=hL.grain X hb j (2*a) (by rw [mul_assoc]; exact mul_pos (by norm_num) hb) le_rfl
  rw [show X.enforce (2*a) (L s y) O=X.enforce (2*a) (L' s y) O from Finset.prod_congr rfl (fun i hi=>(hv i).1.symm)]; by_cases hs : X.enforce (2*a) (L' s y) O=0; · rw [hs,zero_mul,zero_mul]
  apply congr_arg (_ * ·); unfold rootTaylor; apply congr_arg
  symm; apply blueprint J (P:=P) p i (X:= V s y) (X':= V s y) ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩; intro j hj hx
  exact (hv j).2 fun h=>hs (prod_eq_zero (X.ages j _ hx hj) h)
end zest
end YM.LocalTaylorR2.Canvas
