import YM.MS.Orbit.Archive
/-!
# Motion at absolute heat length r. ∫ smooth. Ext curves carry all derivative needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog Wire
open scoped Topology ContDiff Interval
variable {G:Gauge}{A I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F H:Wind.Flow G}{n:Side}{P:ℝ→ Latch.Edge G}
  {J:Cover} {u:E→ℝ}{K:E→ QP} {w x y:tagSmooth E ( BH G ) QP}
lemma cour_s (n:Side): Cour (σcap n):= by
   let S:= Set.range (Coord ( n:=n )); refine ⟨ S, ( finite_range _ ).isCompact,?_⟩; rw [ae_iff]; change σcap n Sᶜ=0; rw [σcap,Measure.finsetSum_apply]; apply Finset.sum_eq_zero; intro i _; rw [Measure.smul_apply,Measure.dirac_apply, Set.indicator_of_notMem]; simp; exact fun h=> h ⟨ i,rfl ⟩
lemma be_sm (p:Cover): ContDiff ℝ ∞ (be p):= by unfold be Tone.bill pairing; refine ContDiff.cexp ( ContDiff.mul contDiff_const (Complex.ofRealCLM.contDiff.comp ?_) ); change ContDiff ℝ ∞ (pairing (embed p)); unfold pairing; fun_prop
lemma flag_sm (p:E→QP)(he:ContDiff ℝ ∞ p)(i:BH G): ContDiff ℝ ∞ (fun x=> flag i (p x)):= by unfold flag weightψ; dsimp only; unfold Tone.bill pairing; refine ContDiff.cexp ( ContDiff.mul contDiff_const (Complex.ofRealCLM.contDiff.comp ?_) ); change ContDiff ℝ ∞ (fun x=>pairing (p x) (offset i.1)); unfold pairing; fun_prop
lemma switch_sm (i:BH G): ContDiff ℝ ∞ (fun x:QP=> switch (i,x)):= by unfold switch; exact (contDiff_const (c:=tick antiZ i)).mul (( flag_sm _ contDiff_id.neg i)|>.pow 2)
lemma flip_f (k:Bool): ContDiff ℝ ∞ (Opp k):= by cases k; exact contDiff_id.neg; exact contDiff_id
lemma flexD (h:flex P) : flex (fun t=> dope (P t)):= fun i j=> (( flag_sm _ contDiff_snd i ).mul ( flag_sm _ contDiff_snd.neg j )) |>.mul (h i j)
lemma flexI (h:flex P): flex (fun t=> valueI (P t)):= fun i j=> (h i j).mul (( switch_sm j ).comp contDiff_snd.neg)
lemma flex_η (b:Bool)(h:flex P): flex (fun t=>ηbone b ( P t )):= by cases b; exact h; exact flexI h
lemma touch_mesh (b:Bool)(hK:flex P)(i j:BH G)(h:Trail x)(he:Trail y)(hp:TouchF F)(hv:TouchF H)(hQ:ContDiff ℝ ∞ u)(ht: ContDiff ℝ ∞ K): ContDiff ℝ ∞ (fun p=> viν b (P (u p)) i j ( F (u p) ) ( H (u p)) (walk0 x p) (walk0 y p) (K p)):= by
    unfold viν; simp_rw [ walk_pitch ]; refine ContDiff.mul ((contDiff_const.mul ( ( hK i j ).comp (hQ.prodMk ht))).mul (contDiff_const.mul ( hp E u ((i,K)::x) (h.cons i K ht) hQ ))) ( hv E u ((j,(Opp b)∘ K)::y) ( he.cons _ _ ((flip_f _).comp ht)) hQ )
abbrev wait (b:Bool)(p:Cover)(K:Latch.Edge G)(F:Law G)(w:Lengths G)(q:QP):= be p q * (∑ i:BH G,∑ j:BH G,K i j q* F ((i,q)::(j,Opp b q)::w))
lemma Hz (b:Bool)(p:Cover)(hp:TouchF F)(h: Trail w)(he:flex P)(hx:ContDiff ℝ ∞ u)(ht:ContDiff ℝ ∞ K): ContDiff ℝ ∞ (fun q=> wait b p (P (u q)) (F (u q)) (walk0 w q) ( K q )):= ( ( be_sm p ).comp ht ).mul (ContDiff.sum (fun i _=> ContDiff.sum fun j _=> ( (he i j).comp (hx.prodMk ht) ).mul (hp E u ((i,K)::(j,(Opp b)∘K)::w) ((h.cons _ _ ((flip_f b).comp ht)).cons i _ ht) hx)))
variable {μ:Measure QP}[IsFiniteMeasure μ](h:Cour μ)
include h
lemma Kit (b:Bool)(p:Cover)(V:Trail w)(s:ContDiff ℝ ∞ u)(H:flex P)(hP: TouchF F): ContDiff ℝ ∞ (fun q=> Θ_pc b μ p (P (u q)) ( F (u q)) (walk0 w q)):= by
    let t:QP×E→ℝ:= fun q=> u q.2; have he:= Hz b p hP (V.comp (f:=Prod.snd) contDiff_snd) H (s.comp contDiff_snd) contDiff_fst; convert! (Lot μ h he).contDiff using 1; ext; simp only [Trail.comp_walk]; rfl -- inference
lemma p_pc (b:Bool)(p:Cover)(hp:flex P)(ht:TouchF F): TouchF (fun t=> Θ_pc b μ p (P t) ( F t ) ):=fun _ _ _ _ _ V s=> Kit h b p V s hp ht -- unused extern h all.S
lemma βwait (b:Bool)(p:Cover)(hp:flex P)(ht:TouchF F)(x:Lengths G)(t:ℝ): Integrable (wait b p ( P t ) ( F t ) x) μ := by
    let w:tagSmooth QP ( BH G ) QP:= station x; have he:=Hz b p ht (station_t x (A:=QP)) hp (contDiff_const (c:=t) ) ( show ContDiff ℝ ∞ (id:QP→QP) from contDiff_id ); apply cafe μ h ; simpa only [station_w,id_eq] using he.continuous -- names
lemma harbor (b:Bool)(p q:Cover)(hV:flex P)(hx:TouchF F)(hY: TouchF H) : TouchF (fun t=> PairV b μ p q (P t) ( F t ) ( H t )):= by
   intro E _ _ u w hw ht; unfold PairV; simp_rw [ wander ]; refine round_scat _ _ _ fun x y he=> ( ( be_sm p ).comp ((hw.splitL he).net0) ).mul ( ContDiff.sum fun i _=> ContDiff.sum fun j _=>?_ ); let V (t:QP×E):= be q t.1 * viν b ( P (u t.2) ) i j ( F (u t.2) ) ( H (u t.2) ) (walk0 x t.2) (walk0 y t.2) t.1;
   apply (Lot μ h ( f:= V) _).contDiff; refine ContDiff.mul ((be_sm q).comp contDiff_fst) ?_; convert! touch_mesh b hV i j ((hw.splitL he).comp (f:=Prod.snd) contDiff_snd) ((hw.splitR he).comp (f:=Prod.snd) contDiff_snd) hx hY ( ht.comp contDiff_snd ) contDiff_fst using 1; ext; simp [Trail.comp_walk] -- using?
omit h [IsFiniteMeasure μ] in
lemma qBirth (hp:flex P)(h: TouchF F): TouchF (fun t=> birth ( P t ) ( F t )):= by
   intro E _ _ f w hw he; unfold birth Hβ; refine contDiff_const.mul ( ContDiff.sum fun i _=> ?_ ); let g (p:E):= root_q ( net (walk0 w p) ) i; have hV:ContDiff ℝ ∞ g:= ( ContDiff.neg ( (contDiff_const (c:=((2:ℝ)⁻¹))).smul hw.net0 ) ).add (contDiff_const (c:=Coord i)); refine ContDiff.sum fun k _=>ContDiff.sum fun j _=>( (hp k j).comp (he.prodMk hV)).mul ( h E f ( (k,g)::(j,g)::w ) ( (hw.cons _ _ hV).cons _ _ hV ) he ) -- wf ∞ dims
end YM.MS.Orbit
