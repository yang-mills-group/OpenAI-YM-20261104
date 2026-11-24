import YM.OPE.Compatible.Lines.Hinge
/-! evade *all* incomparable vertex position ties (not just simultaneously visible). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice
open scoped Topology BigOperators Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)(Q:Finset X)
variable {H:Crown Q}{s:X→ℝ}(g:Sight)(x:X→ E4)(f:Wing D Q→ℝ)
set_option quotPrecheck false
local notation "Y"=> fun h=> reload D Q s g x h
-- all whose motion variables already fixed must live in Screen now
def angleClear (x:X→E4)(M:Finset (Wing D Q)):Prop:= ∀ u∈allUp D Q,∀ v∈allUp D Q, ¬ u≤v → ¬ v ≤ u → (∀ i∈M,¬flex D Q i u v) → ∀ a:Axis,x u a≠ x v a
lemma shutter (x:X→ E4):angleClear D Q x Finset.univ:=by
   intro u hu v hv he hq hb
   let i: legs D Q := ⟨u,Finset.mem_erase.mpr ⟨fun h=> by rw [h] at he; exact he bot_le, hu⟩⟩; exact False.elim (hb (i,0) (Finset.mem_univ _) (fun h=>he (h.mp (show u≤u from le_rfl))))
lemma shutter_final (h:Crown Q)(x:X→E4)(he:angleClear D Q x ∅): Screen (picked (brim D Q) x):=by
    intro a i j hi; apply Subtype.ext; by_contra hh; exact he _ (Finset.mem_union_right _ i.2) _ (Finset.mem_union_right _ j.2) (brim_apart D Q h i.2 j.2 hh) (brim_apart D Q h j.2 i.2 (Ne.symm hh)) (fun b ht=>False.elim (Finset.notMem_empty _ ht)) a hi -- inference
lemma holes {i:Wing D Q}{M:Finset (Wing D Q)}(hi:f i=0)(h:angleClear D Q (Y f) (insert i M))(hp:0< s (par D i.1.1)) :
   ∃ T:Finset ℝ,T.card ≤ Fintype.card (X×X×Axis)∧ ∀ r∉T, angleClear D Q (Y (Function.update f i r)) M:=by
   let Van(u v:X)(j:Axis):= Y f u j-Y f v j; let e:=FrameRead.trail (g.code i.2); let t:=s (par D i.1.1); let U(a:X)(j:Axis):= (if inMotion D Q i a then t else 0)*e j
   let V(a:X×X×Axis) := - Van a.1 a.2.1 a.2.2 /(U a.1 a.2.2-U a.2.1 a.2.2)
   have hy(w r j):Y (Function.update f i r) w j= Y f w j+r * U w j:=by
       change reload D Q s g x (update f i r) w j=_; rw [differential]; have h' : (Function.update f i 0)=f:= by rw [← hi,Function.update_eq_self]; -- name
       rw [h', PiLp.add_apply,PiLp.smul_apply]; change _ + (r*(if inMotion D Q i w then t else 0)) * e j = _; unfold U
       ring
   refine ⟨Finset.univ.image V, (Finset.card_image_le).trans_eq (Finset.card_univ), fun r hr u hu v hv hh hh' hK j hl=>?_⟩
   rw [hy,hy] at hl
   by_cases hq:flex D Q i u v
   · apply hr; refine Finset.mem_image.mpr ⟨(u,v,j),Finset.mem_univ _,?_⟩; unfold V; dsimp only; have he : U u j-U v j≠0:=by
         have he: e j>0:=trail_eye ..; by_cases hi:inMotion D Q i u; have hv:¬inMotion D Q i v:=fun h=>hq (iff_of_true hi h);
         · simp [U,hi,hv,he.ne',show t≠0 from hp.ne']
         have hx:=not_not.mp (fun hh'':¬inMotion D Q i v=>hq (iff_of_false hi hh'')); simp [U,hi,hx,he.ne',show t≠0 from hp.ne']
     apply (div_eq_iff he).mpr; unfold Van; linarith only [hl]
   apply h _ hu _ hv hh hh' (fun j hj=> (Finset.mem_insert.mp hj).elim (fun h=> h.symm ▸ hq) (hK j)) j
   have hz:=not_not.mp hq; have hy: U u j= U v j:=by unfold U; congr 1; simp only [show inMotion D Q i u ↔ inMotion D Q i v from hz]; -- remaining
   rw [hy] at hl; linarith
end YM.OPE.Arboreal.Trace
