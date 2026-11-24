import YM.SchemeConversionRG11.FirstW.Fade.Local
/-! Local distribution limit witnesses against variable tensor tapes with actual perturbative differentiation. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Topology
open scoped BigOperators Classical
variable {T:Itinerary} {E F: Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
variable {f g:Hall T E}
-- may be generalized to any CLM test (dual E)
def tollH (T:Itinerary) (f:Hall T E)(p:Hall T (E→L[ℝ] ℝ))(i:ℕ):= T.gap i ^4 * ∑ x:Site (T.period i), p i x (f i x)
def Dusk (T:Itinerary)(f:Hall T E): Prop:=∀ r R:ℝ,r>0 → r<R → ∀ p:Hall T (E→L[ℝ] ℝ), Placed T r p → ∀ Y, Score T (Town R) p Y → Helen (tollH T f p)
lemma forward_lim {c:ℕ→Side}{k:ℕ}{W:E4→E}(hc:MarkGrid T c)(hk:k≤3)(h:Meets T {x:E4|x≠0} f W)(hv:SaveB T k f):Dusk T f:= by
 intro r R hr he p H Y hY
 exact ⟨_, (cap_power hv hc h he hr.le hk hY.identity H (ContinuousLinearMap.id ℝ (E→L[ℝ] ℝ)).flip).2⟩ -- flip works
lemma Dusk.rake (h:Dusk T f)(q:Dusk T g): Dusk T (f+g) := by
 intro r R hr he p H Y hY; obtain ⟨x,h⟩:=h _ _ hr he p H _ hY; obtain ⟨v,q⟩:=q _ _ hr he p H _ hY; refine ⟨x+v,(h.add q).congr fun i=>?_⟩; simp only [tollH,Pi.add_apply,map_add, Finset.sum_add_distrib,mul_add]
lemma dusk_zero : Dusk T (0:Hall T E):=fun _ _ _ _ p _ _ _=> ⟨0, Tendsto.congr (f₁:=fun _=>(0:ℝ)) (fun i=>by simp [tollH]) tendsto_const_nhds⟩
lemma Dusk.sum {I:Type*}(w:Finset I){f:I→Hall T E}(h:∀ i∈w,Dusk T (f i)): Dusk T (∑ i∈w,f i):= by
 induction w using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact dusk_zero | insert i w hw ih=> rw [Finset.sum_insert hw]; exact Dusk.rake (h i (Finset.mem_insert_self ..)) (ih (fun j hj=>h _ (Finset.mem_insert_of_mem hj)))
def mailR (T:Itinerary)(f:Hall T E)(s:Cover): Hall T E:= fun i x=>f i (x+wrap (T.period i) s)
lemma penR {n:Side}(f:Site n→E)(p: Site n→ E→L[ℝ] ℝ)(s:Site n): ∑ x:Site n,p (x+(-s)) (f x)=∑ x:Site n,p x (f (x+s)) := Eq.symm (by simpa using (Equiv.sum_comp (Equiv.addRight s) (fun x=> p (x+-s) (f x)))) -- simp maybe
lemma Dusk.mail (h:Dusk T f)(s:Cover): Dusk T (mailR T f s):=by
 intro r R hr hp p H Y hY; obtain ⟨q,hq,hR⟩:=exists_between hp; obtain ⟨v,B⟩:=h q R (lt_trans hr hq) hR (mailR T p (-s)) (H.flow hq _) Y (hY.nudge _)
 refine ⟨v,B.congr fun i=>?_⟩; unfold tollH mailR; simp_rw [map_neg]; rw [penR]
lemma Dusk.shape (h:Dusk T f)(L:E→L[ℝ] F): Dusk T (fun i x=>L (f i x)):=by
 let B : (F→L[ℝ] ℝ) →L[ℝ] (E→L[ℝ] ℝ):= (ContinuousLinearMap.compL ℝ E F ℝ).flip L
 intro r R hr he p H Y hY; apply h _ _ hr he (fun i x=> B (p i x)) (Eventually.mono H (fun i hi x hx=> hi x (fun h'=>hx (by simp only [h',map_zero])))) (fun D v=> B (Y D v)) (hY.map B)
lemma Dusk.scale (h:Dusk T f)(r:ℝ): Dusk T (r • f):= h.shape (r • ContinuousLinearMap.id ℝ E)
lemma score_neg {S:Set E4}{Y:Sheets E}(h:Score T S f Y) : Score T S (-f) (-Y):= by simpa only [Pi.neg_def] using! Score.map (-ContinuousLinearMap.id ℝ E) h
lemma score_diff {S:Set E4}{Y W:Sheets E}(h:Score T S f Y)(q:Score T S g W): Score T S (f-g) (Y-W):= by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.plus (score_neg q)
lemma Dusk.sub (h:Dusk T f)(q:Dusk T g) : Dusk T (f-g):=by rw [sub_eq_add_neg]; apply Dusk.rake h; simpa using q.scale (-1)
lemma place_air {p:Hall T E}{r R:ℝ}(h: Placed T r p)(e:r<R)(a:Axis): Placed T R (ray a p) := by
 let q:=mailR T p (step a); filter_upwards [h,h.flow e (step a)] with i hi H x hx
 by_cases h:p i x=0; · refine H x (fun he=> hx ?_); simp only [wrap_step] at he; simp [ray,surface,combine,up,h,he]
 exact (hi x h).trans e.le
lemma settle_air (a:Axis) (p:Hall T (E→L[ℝ] ℝ))(f:Hall T E)(i:ℕ): tollH T (ray a f) p i=tollH T f (-(mailR T (ray a p) (-step a))) i := by
 unfold ray mailR tollH surface; simp only [map_neg,wrap_step, Pi.neg_apply,combine,up, Pi.smul_apply,map_smul,map_sub,smul_apply, neg_apply,sub_apply,add_assoc, neg_add_cancel,add_zero,smul_eq_mul,Finset.sum_neg_distrib, mul_sub,Finset.sum_sub_distrib,←Finset.mul_sum]; rw [penR]; ring
lemma Dusk.ray_pay (h:Dusk T f)(a:Axis): Dusk T (ray a f):= by
 intro r R hr hp p H Y hY; obtain ⟨s,hs,hR⟩:=exists_between hp; obtain ⟨t,ht,hT⟩:=exists_between hR
 let q:= mailR T (ray a p) (-step a)
 have ht': Placed T t (-q):= Eventually.mono (show Placed T t q from (place_air H hs a).flow ht _) (fun i hi x hx=> hi x (by simpa using hx))
 obtain ⟨v,hp⟩:= h t R (hr.trans (hs.trans ht)) hT (-q) ht' (-(fun D=>Y (D++[a])):Sheets (E→L[ℝ] ℝ)) (score_neg ((hY.insect [a]).nudge _))
 exact ⟨v,hp.congr fun i=> (settle_air a p f i).symm⟩
lemma Dusk.cut (h:Dusk T f)(D:List Axis): Dusk T (surface D f):= by induction D with | nil=> rw [surface_root]; exact h | cons i D ih=> rw [show i::D=[i]++D from rfl,←surface_surface]; exact ih.ray_pay i
end YM.RG11.FirstW
