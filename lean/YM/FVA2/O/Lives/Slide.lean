import YM.FVA2.O.Lives.Budget
/-!
# Every-scale derivative for the cycle
Use *two* compact rapid bounds. No dependence on q allowed in the time neighborhood.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire
open scoped Topology ContDiff
variable {G:Gauge}{I:Type}{i:I}{F F' H H' : Glade G I}{U V:Planet G I}{z:ℝ}
lemma passes (hU:BackF U)(hF:Warm F false): Pass (U i z) (F i z) planeF:= fun l=> Sat_W hF hU (fun _=> Geo.Coherent) i z l (fun x=>Bool.noConfusion x)
lemma covers (i:I) (v:ℝ) (hU:BackF U)(hF:Warm F false)(l:List (Lane4 G)): let T:=‖v‖+1; ∃ c:QP→ℝ,Integrable c planeF ∧ ∀ t∈Set.Icc (-T) T,∀ p, ‖trc (U i t) p (F i t) l‖≤ c p:= by
    intro T; let V:= Job.single (camp T); have hT:T≥0:= by unfold T; positivity
    have hh : pole V (fun (k:camp T) (u: QP × ℝ)=> trc (tap U i T k) u.1 (tap F i T k) (sail (ray l) u.2)) 1:= by
        convert! topCycle ( Lease.highp ( hF.cost i T hT )) ( hU.cost i T hT) ( w:=ray l ) (fun i=>Bool.noConfusion i) (fun _=>zero_le_one) (fun _=>zero_le_one) using 1; ext; simp [positive,cw]
    obtain ⟨d,hD,hW⟩:= Job.funds (camp T) Geo.Coherent; obtain ⟨C,hC,k,H⟩:= hh.dominates 0 d; let v':camp T:= ⟨(),v,existsC v⟩; refine ⟨fun u=> C*2^k*V.dust d v' u, (hW.integrable v').const_mul (C*2^k),fun t ht u=> ?_⟩; specialize H (⟨ (),t,ht⟩:camp T) u 1 trivial; unfold V; simp only [ V,norm_iteratedFDeriv_zero, Pi.one_apply,ray_sail, show ‖(1:ℝ)‖=(1:ℝ) by simp, tx, one_add_one_eq_two,pow_zero,mul_one ] at H; exact H
abbrev Velocity (F F': Glade G I): Prop:= ∀ i t, Zip (F i) (F' i t) t
-- local standing assumptions: `Cohere` is always planeF here.
lemma orbit_V (hF:Warm F false)(hp:Warm F' false)(ht: Velocity F F')(hh:BackF U)(hv:BackF V)(hr:∀ i t,Heat.Jet (U i) (V i t) t): Velocity (fun i t=> orbit (U i t) planeF (F i t)) (fun i t=> orbit (V i t) planeF (F i t)+orbit (U i t) planeF (F' i t)) := by
    intro i t l; let T:= ‖t‖+1; let W(u:ℝ)(p:QP):= trc (U i u) p (F i u) l; let X(u:ℝ)(p:QP):= trc (V i u) p (F i u) l + trc (U i u) p (F' i u) l; have hW(u:ℝ):Integrable (W u) planeF:= passes hh hF l; let C:= passes (i:=i) (z:=t) hv hF; let D:= passes (i:=i) (z:=t) hh hp
    obtain ⟨a,ha,A⟩:= covers i t hv hF l; obtain ⟨b,hb,B⟩:= covers i t hh hp l; have hI(x)(p): HasDerivAt (fun s=> W s p) (X x p) x:= by unfold W X; simp_rw [at_trc, ← Finset.sum_add_distrib]; exact HasDerivAt.fun_sum fun u _=> HasDerivAt.fun_sum fun v _=> (hr i x u v p).mul (ht i x _)
    have he := (hasDerivAt_integral_of_dominated_loc_of_deriv_le ( Job.lamp t ) (.of_forall (fun x=> (hW x).1)) (hW t) ((show Integrable (X t) planeF from (C l).add (D l)).1) (.of_forall (fun p u hu=> (norm_add_le ..).trans (show _≤ (a+b) p from add_le_add (A u hu p) (B u hu p)))) (ha.add hb) (.of_forall (fun p x hx=> hI x p))).2
    unfold X at he; rw [integral_add (C l) (D l)] at he; dsimp only; rw [ finite_cc planeF C, finite_cc planeF D, funext (fun x=> congr_fun (finite_cc planeF ( passes (i:=i) (z:=x) hh hF)) l) ]; exact he
lemma line_jet (_:I)(t:ℝ): Heat.Jet (lineB G) (lineD G t) t:= by unfold lineD; rw [cue]; exact trigger G t 0
lemma tree_velocity (h:Velocity F F')(hx:Velocity H H') : Velocity ( fun i t=> tree Landau.parity (lineB G t) (F i t) (H i t)) ( fun i t=> tree Landau.parity (lineD G t) (F i t) (H i t)+ tree Landau.parity (lineB G t) (F' i t) (H i t)+ tree Landau.parity (lineB G t) (F i t) (H' i t) ) := fun i t=> tree_zip (fun t=>reverse_b G t 0) (by unfold lineD; rw [cue]; exact reverse_c G t 0) (line_jet i t) (h i t) (hx i t)
end YM.FVA2.O.Lives
