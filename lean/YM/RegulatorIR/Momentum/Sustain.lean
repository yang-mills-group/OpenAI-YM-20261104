import YM.RegulatorIR.Momentum.Vacant
import YM.RegulatorIR.Oracle.Life

/-!
# Forward costs ALL motions, provided BEFORE choosing Length
No pre-cost used for Phi or tree. K from pinned Q. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Exterior Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Sources Oracle Oracle.Quarry RG Bloch Precision Lattice Tree PertExtension Geometry.Field
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {G:Gauge}{P:Patch}{σ F:ℝ}{u m:ℕ}
lemma ribbon (i : Long G.ColorIndex)(L:Side)(x:Cover)(t:Site L)(h:area i=Sources.child L x t):(blockQ G L).boom i=x:=by
 obtain ⟨⟨p,b⟩,y⟩:=i; change p=_ at h; subst p;exact congr_arg Prod.fst (landFull L x t (Exterior.coord b,y))
lemma lead_distance (t:Side) (x: Long G.ColorIndex) (v:Long G.ColorIndex) :
 awayZ (area x) v t.val ≤ extent ((blockQ G t).boom x-(linksQ G).boom v)+4:=by
 obtain ⟨⟨z,b⟩,hz⟩ := reachesR t (area x); rw [ribbon x t z b hz.symm]; change award t.val * extent _ ≤ extent (z-area v)+4;rw [← hz];
 rw [show child t z b - t.val • area v=t.val • (z-area v)+Lattice.lift b from by unfold Sources.child;rw [smul_sub];abel]
 apply le_trans (mul_le_mul_right (extent_add ..) _); rw [extent_n, mul_add, ← mul_assoc, show award t.val*(t.val:ℝ≥0∞)=1 from ENNReal.inv_mul_cancel (by exact_mod_cast t.property.ne') (by finiteness), one_mul]
 apply add_le_add_right
 have hv: extent (Lattice.lift b) ≤ (t.val:ℝ≥0∞)*4 :=by
    unfold extent; exact_mod_cast (show size (Lattice.lift b)≤t.val*4 from by
      have hh(v:Axis): (Lattice.lift b v).natAbs ≤ t.val:=by have he:=lift_centers b v; omega
      apply le_trans (Finset.sum_le_sum (f:=fun i=> (Lattice.lift b i).natAbs) (g:=fun _=> t.val) (fun i _=> hh i)); simp [Axis];omega )
 exact (mul_le_mul_right hv _).trans_eq (by rw [← mul_assoc, show award t.val*(t.val:ℝ≥0∞)=1 from ENNReal.inv_mul_cancel (by exact_mod_cast t.property.ne') (by finiteness),one_mul])
lemma forecast_d {t:Side} {K:Layer (Long G.ColorIndex) (Long G.ColorIndex)}{p:ℝ≥0∞} (h:chestE (blockQ G t) (linksQ G) σ K p)(x)(u:ℕ)(hs:0<σ): quota (K x) (fun i=>quotes (area x) i t.val u) ≤ p*ENNReal.ofReal (scar σ u):=by
 apply le_trans _ (mul_le_mul_left (h x) _); rw [← quota_raised]; apply quota_mono; intro i
 let k:= size ((blockQ G t).boom x-(linksQ G).boom i); apply le_trans (b:=(1+(k:ℝ≥0∞)+4)^u) ?_
 · have ht:= ENNReal.ofReal_le_ofReal (scars σ u hs |>.2 k)
   unfold liftsE; rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm];
   suffices h : (1+(k:ℝ≥0∞)+4)^u=ENNReal.ofReal ((1+(k:ℝ)+4)^u) by rw [h];exact ht
   rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_add zero_le_one (by positivity)];simp
 unfold quotes; rw [add_assoc]; exact pow_le_pow_left' (add_le_add_right (lead_distance ..) _) _
lemma cabin_callG (b:Regalia G.ColorIndex)(t: Side)(x:Cover)(z:Site t): (blockQ G t).cabin (ask (child t x z) b)= (z,Exterior.coord b.1,b.2):= congr_arg Prod.snd (landFull t x z (Exterior.coord b.1,b.2))
variable (R: Cross P.L (TypeFace 1) (TypeFace 1))
open Next.Free (cover_step carryStep)
lemma chartQ (x:Cover)(z:Site P.L) (a:Axis) :child P.L x z+hop a=child P.L (x+Next.Free.carryStep a z) (z+Lattice.step a):=by
 have he:= cover_step P.odd_side a z; unfold Sources.child;rw [smul_add, add_assoc (P.L.val • x), show hop a=Lattice.step a from by ext i;simp]; rw [← he]; abel
lemma spring_pay (p:Cover)(b:Regalia G.ColorIndex) (a:Axis): spring (windA (ruling P G R) p b) a= windA (ruling P G (Precision.forwardC P.L R a)) p b :=by
 ext1 i;ext1 j; change ruling P G R (ask (p+(i+hop a)) b) j -ruling P G R (ask (p+i) b) j=ruling ..
 obtain ⟨⟨d,t⟩,hd⟩:= reachesR P.L (p+i); rw [← add_assoc,← hd,chartQ]
 unfold ruling; rw [lade_eq, lade_eq,lade_eq,cabin_callG b,cabin_callG b]; have HH v x:(blockQ G P.L).boom (ask (child P.L v x) b)= v:= ribbon _ _ _ _ (show _ = child P.L v x from rfl); rw [HH, HH]
 unfold adult; split <;> rename_i h
 · unfold forwardC; change _-_ = R _ _ ((linksQ G).boom j-d-carryStep a t)-R _ _ _; rw [← sub_add_eq_sub_sub]
 abel
lemma stencil_pay (p:Cover)(b:Regalia G.ColorIndex)(l:List Axis): journey (windA (ruling P G R) p b) l=windA (ruling P G (advanceC P.L R l.reverse)) p b:=by
 induction l using List.reverseRecOn with
 | nil=>rfl
 | append_singleton l a ih=>rw [onward,ih]; simp only [List.reverse_append,List.reverse_singleton,List.cons_append,List.nil_append,advanceC]; exact spring_pay ..
lemma grant (G:Gauge){P:Patch}(R: Cross P.L (TypeFace 1) (TypeFace 1))(hs:0<σ)(hc:0≤F)(hp :∀ l:List Axis,l.length≤m→(advanceC P.L R l).strip σ (F/(P.L.val:ℝ)^(1+l.length))) : PriceW (ruling P G R) P.L.val u m (pack_c G u σ F):=by
 constructor; intro p v l ht x;rw [stencil_pay]; let A:= advanceC P.L R l.reverse
 have h : A.strip σ (F/(P.L.val:ℝ)^(1+l.length)):=by simpa only [List.length_reverse] using hp l.reverse (by simpa)
 have hw : 0 ≤ F/(P.L.val:ℝ)^(1+l.length):=by positivity
 have he:= forecast_d (roots _ _ (adult_price G P A h hw) : chestE (blockQ G P.L) (linksQ G) σ (ruling P G A) _) (ask (p+x) v) u hs
 apply he.trans_eq;rw [div_eq_mul_inv,ENNReal.ofReal_mul hc,ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_natCast,ENNReal.inv_pow]
 unfold pack_c award;ring
end YM.RegulatorIR.Momentum
