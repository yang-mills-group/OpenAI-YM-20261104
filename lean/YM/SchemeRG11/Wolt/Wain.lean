import YM.SchemeRG11.Wolt.Descent
/-! Post T: trim enough offset to leave summable. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Wolt
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T: Align.Itinerary}{c:ℕ→Sky G n→ℝ}{R r:ℝ}{B:Window} {F:Falls G}{p:pLabel G}
lemma ward_walk (B:Window)(h:IsWeightedHomogeneous generation p n)(hp:B.rOut<r)(hv:r<R)(hB:Blue T R F)(hc:Tone c)(he:Twin T R n F (shapeV T c)): Finishes (fun i=> T.gap i ^(-(n:ℤ))* (∑z∈gateY T r i,(aeval (F i) (smoke T B p i z) -spry T c n (smoke T B p i z) i))) :=by
 let f:= smoke T B p
 let u:ℤ:= (n:ℤ)+4
 let A:Slate:=fun i z=> aeval (F i) (f i z)
 let L:Slate:=fun i z=>aeval (shapeV T c i) (f i z)
 let g:Slate:=fun i z=> spry T c n (f i z) i
 let e:Slate:=fun i z=>(T.gap i)^(-u)*(A i z-g i z)
 have Hr:r>0:= B.rIn_pos.trans (B.rIn_lt_rOut.trans hp)
 have S:Sigil T n u f:= swell (crystalline ..) h _
 have H:Defect T r R (n+1) F (shapeV T c) u f:= swell (summit hv Hr hB c he) h _ -- ambiguous
 have V:= hind (R:=r) S hc n
 have ht : Streams T (fun p=> ‖p‖<2*R) (-u) (A-g):= H.handy.sub (uplink S hc n)
 have hd:Local T r ((n:ℤ)+1) ((n:ℤ)+1-u) (A-g):=by
    rw [show A-g=A-L+(L-g) from by abel]; have hh:= H.charge; rw [Nat.cast_add_one] at hh; exact Wall.add (f:=A-L) hh (g:=L-g) V
 have hk : Local T r (-3) (-3) e:=by
    convert (Wall.scale (S:=Near T r) (-u)).mul hd using 1 <;> first|dsimp [u]; omega|rfl
 obtain ⟨C,hC,W⟩:=hk
 have hE : ∀ᶠ i in atTop,∀ z∉gateY T r i,e i z=0:=(banished (T:=T) hp p).mono (fun i h q hx=>by simp only [e,A,f,g,h q hx,spry,map_zero, sub_zero,mul_zero])
 have hK:∀ᶠ i in atTop,∀ z ∈ gateY T r i, |e i z| *baseU T i z^3 ≤ C:=by
    filter_upwards [W] with i hi z hz
    have hh:=T.positive i; have hk:=World.d_pos z; have ht:0≤baseU T i z:=(mul_pos hh hk).le
    apply le_trans (mul_le_mul_of_nonneg_right (hi z ((gate_iff ..).mp hz)) (by positivity)); unfold baseU; rw [zpow_neg,zpow_neg]; field_simp; simp
 have hx(y:E4)(hy:y≠0):Finishes (fun i=> e i (stake (T.gap i) y)):=by
    let Z i:=stake (T.gap i) y
    by_cases q:‖y‖<2*R; · exact ht y hy q Z (follows y)
    have hu := Tendsto.norm (show Tendsto _ atTop _ from follows (T:=T) y); apply (Finishes.const 0).same
    filter_upwards [hu.eventually (lt_mem_nhds (show 2*r< ‖y‖ by linarith)),hE] with i hi ht
    exact (ht (Z i) (fun e=> not_lt.mpr ((cord T i _).trans (by linarith only [show baseU T i (Z i)≤ r from (gate_iff ..).mp e])) hi)).symm
 apply (travellers hE hC.le (gate_d ..) hK hx).same
 filter_upwards with i; change (T.gap i)^4 *∑ _∈_,_= _ -- parentheses
 unfold e; rw [←Finset.mul_sum,←mul_assoc]; unfold u; have he:= T.positive i; rw [zpow_neg,zpow_neg,zpow_add₀ he.ne']; apply congr_arg₂ (·*·); · field_simp
 rfl
-- local point remainder for FIXED stencils, stronger derivative gains already at anchor
lemma offsetL (hr:0<R)(hB:Blue T R F)(u:Shaft G): Finishes (fun i=>F i u):=by
 let x:=u.1.1; have he := hB.came u.2 u.1.2 0 0 (by rw [norm_zero]; linarith) _ (World.Along.base x); apply ((Finishes.of T.cutoff).mul he).same; filter_upwards with i; rw [←mul_assoc,Multiset.card_zero]; simp only [Nat.cast_zero,zero_add,zpow_neg,zpow_one,mul_inv_cancel₀ (T.positive i).ne',one_mul]; rcases u with ⟨⟨_,_⟩,_⟩; rfl
lemma season {I:Type*} (x:ℕ→ I→ℝ)(hx:∀i,Finishes (fun k=> x k i))(v:Paper I ℝ): Finishes (fun i=> aeval (x i) v):=by induction v using MvPolynomial.induction_on with
 | C c=> simp_rw [aeval_C]; exact Finishes.const _
 | add v w a b=> simp_rw [map_add]; exact a.add b
 | mul_X v j h=> simp_rw [map_mul,aeval_X]; exact h.mul (hx j)
lemma locker (hc:Tone c)(s:Sky G n): Finishes (fun i=>rooms T c i s):= (higher _ (by unfold inkAge degree; omega)).mul (hc s)
lemma boon (hc:Tone c)(p:vellum G): Finishes (fun i=>aeval (shapeV T c i) p):=by simp_rw [cost_z]; exact season _ (locker hc) _
lemma credit {x:ℕ→ℝ}(h:Finishes x): x=O[atTop] (fun _=> (1:ℝ)):=by
 obtain ⟨C,hC,H⟩:=(bond (T:=itinerary (2:Lattice.Side) (by decide)) h); apply IsBigO.of_bound C; filter_upwards [H] with i hi; simpa only [zpow_zero,mul_one,norm_one,Real.norm_eq_abs] using hi (0:Cover) trivial
lemma firstlight {a b g:ℕ→ℝ}(h:a=O[atTop] g)(w:Finishes b): (fun i=>a i*b i) =O[atTop] g:=by have e:= h.mul (credit w); simpa only [Pi.mul_apply,mul_one] using e
lemma familiar (c:ℕ→ Sky G n→ℝ) (hr:R>0)(hB:Blue T R F)(hc:Tone c)(he:Twin T R n F (shapeV T c))(P:vellum G): (fun i=> aeval (F i) P-aeval (shapeV T c i) P)=O[atTop] latch T ((n:ℤ)+1):=by
 induction P using MvPolynomial.induction_on with
 | C t=> simp_rw [aeval_C,sub_self]; apply isBigO_zero
 | add p q hp hq=> simp only [map_add,add_sub_add_comm]; exact hp.add hq
 | mul_X p a h=>
    simp only [map_mul,aeval_X]
    have hw : (fun i=> F i a-shapeV T c i a) =O[atTop] latch T (n+1):=by
       rcases a with ⟨⟨x,j⟩,q⟩; exact noted (he q j 0) hr x
    convert! (firstlight h (offsetL hr hB a)).add (firstlight hw (boon hc p)) using 1; funext i; ring
lemma point_hi (hc:Tone c)(v:vellum G): (fun i=> aeval (shapeV T c i) v- spry T c n v i)=O[atTop] latch T ((n:ℤ)+1):=by
 simp only [cost_z,spry]; simp_rw [hiPrice _ (c:=c) (inlay G n v).support (Finset.Subset.refl _)]
 apply istr _ ?_; intro i _
 split; · simp only [zero_mul]; apply isBigO_zero
 next w=>
   refine IsBigO.const_mul_left (firstlight ?_ (toneS i hc)) _ -- function unify
   apply hatch_iff.mpr; refine ⟨1,zero_lt_one,?_⟩; filter_upwards [T.cutoff.eventually (ge_mem_nhds zero_lt_one)] with j hj
   rw [one_mul, abs_of_pos (zpow_pos (T.positive _) _)]; have hp:0 < T.gap j:=T.positive _; rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) from (Nat.cast_add_one n).symm, bill,zpow_natCast,zpow_natCast]; exact pow_le_pow_of_le_one hp.le hj (by omega)
lemma avails (hr:0<R)(hc:Tone c)(v:vellum G)(hB:Blue T R F)(he:Twin T R n F (shapeV T c)): (fun i=> aeval (F i) v - spry T c n v i)=O[atTop] latch T ((n:ℤ)+1):=by convert! (familiar c hr hB hc he v).add (point_hi hc v) using 1; funext i; abel
end YM.SchemeRG11.Wolt
