import YM.OPE.Compatible.Arch.Cedar
/-!
# uniformly polynomial local expansions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ E][FiniteDimensional ℝ F]
local notation "Lf" => Tested.germ
open Zone ScriptJ
local notation "R" => Radial.zone (E:=E)
abbrev Cape (A:ℝ→ E →ℝ) (p: ScriptJ E):= Bears 1 A p
def Pawn (A:ℝ→ E→ℝ):Prop:=∃ p,Cape A p
namespace Pawn
variable {A C:ℝ→ E →ℝ}{p: ScriptJ E}{u:E→ℝ}
omit [FiniteDimensional ℝ E] in
lemma compare (h:Pawn A)(he: ∃ a>0,∀ x t,0<t→ t*(R).w x ≤ a→ A t x=C t x): Pawn C:= h.elim fun p hp=>⟨p,hp.equiv he⟩
omit [FiniteDimensional ℝ E] in
lemma stay (A: ScriptJ E)(hp:A.B): Pawn (quitt A):=⟨_,Bears.grade hp (fun _=>le_rfl)⟩
lemma cash (h:Pawn A)(hp:Pawn C): Pawn (A*C):= h.elim fun p h=> hp.elim fun q hp=> ⟨p*q,by simpa only [one_mul] using h.ascent hp⟩
omit [FiniteDimensional ℝ E] in
lemma sum (h:Pawn A)(hp:Pawn C): Pawn (A+C):= h.elim fun _ h=> hp.elim fun _ hp=>⟨_,h.piled hp⟩
omit [FiniteDimensional ℝ E] in lemma humA (h:Bond u):Pawn fun (_:ℝ) x=> u x:= (stay _ (lower h)).compare ⟨1,one_pos,fun x t ht _=>by simp [quitt,low,JetS.atK]⟩
omit [FiniteDimensional ℝ F] in lemma rayA (w:E→ F)(f:F→ℝ)(hf:Bond f)(h:∀ ℓ:Module.Dual ℝ F,Pawn fun _ x=>ℓ (w x)): Pawn (fun _ x=>f (w x)):= by induction hf with
     | keep c=> exact humA (Bond.keep c)
     | glyph c=> exact h c
     | add _ _ a b=> exact a.sum b
     | mul _ _ a b=> exact a.cash b
omit [FiniteDimensional ℝ F] in lemma join {w:ℝ→ E→ F}(f:F→ℝ)(hf:Bond f)(h:∀ ℓ:Module.Dual ℝ F,Pawn fun t x=>ℓ (w t x)): Pawn (fun t x=> f (w t x)) := by induction hf with
     | keep c=> exact humA (Bond.keep c)
     | glyph c=> exact h c
     | add _ _ a b=> exact a.sum b
     | mul _ _ a b=> exact a.cash b
private lemma jetting (f:E→ℝ)(k: ℕ): Bond (Radial.jet f k) := (Bond.keep _).mul (Bond.multiline (iteratedFDeriv ℝ k f 0) (fun _ : Fin k=>id) (fun _ ℓ=> Bond.glyph ℓ))
abbrev mold (f:E→ℝ)(k:ℕ): ScriptJ E:=fun x=>⟨Radial.jet f k x,Radial.jet f (k+1) x,Radial.jet f (k+2) x⟩
lemma calm {f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0): Cape (fun (t:ℝ) x=> f (t • x)) (mold f 0):= by
     refine ⟨Xbond (jetting ..) (jetting ..) (jetting ..),?_⟩; convert! (Radial.ordinary f h).fits 2 using 2; ext1 i; ext1 x; simp only [quitt,Zone.eval,JetS.atK]; simp [Finset.sum_range_succ]
lemma hill {f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0)(hf:f 0=0): Cape (fun (t:ℝ) x=> t⁻¹*f (t • x)) (mold f 1):=by
     obtain ⟨δ,C,hδ,hC,hq⟩:= Radial.deposition f 3 h; refine ⟨Xbond (jetting ..) (jetting ..) (jetting ..),fun _=>le_rfl, ⟨δ,C,4,hδ,hC,?_⟩⟩
     intro x t ht hm; let w:= (R).w x; have hw: ‖x‖ ≤ w:= by simp [w,Radial.zone]
     have hh:= hq x t ht ((mul_le_mul_of_nonneg_left hw ht.le).trans hm)
     simp only [quitt,JetS.atK,Pi.sub_apply]; rw [← mul_le_mul_iff_of_pos_left ht]; nth_rw 1 [← abs_of_pos ht, ← Real.norm_eq_abs]; rw [← norm_mul,mul_sub, ←mul_assoc t, mul_inv_cancel₀ ht.ne',one_mul]; rw [show t*(Radial.jet f 1 x+t • (Radial.jet f (1+1) x)+(t^2) • (Radial.jet f (1+2) x))=Zone.eval (Radial.jet f) 3 t x by simp [Zone.eval,Finset.sum_range_succ, hf];ring]
     refine hh.trans ?_; rw [show t * (C*_ * _ * t^3)= C*w^4*t^(3+1) by change t*(C*w^4*1*t^3)=_;ring]; gcongr
lemma trio {f:E→ℝ}(h:Radial.Stationary f): Cape (fun (t:ℝ) x=> f (t • x)/t^2) (mold f 2):=by
     obtain ⟨δ,C,hδ,hC,hq⟩:= Radial.deposition f 4 h.smooth; refine ⟨Xbond (jetting ..) (jetting ..) (jetting ..),fun _=>le_rfl, ⟨δ,C,5,hδ,hC,?_⟩⟩
     intro x t ht hm; let w:= (R).w x; have hw: ‖x‖ ≤ w:= by simp [w,Radial.zone]
     have hh:= hq x t ht ((mul_le_mul_of_nonneg_left hw ht.le).trans hm)
     simp only [quitt,JetS.atK,Pi.sub_apply]; have he:= pow_pos ht 2; rw [←mul_le_mul_iff_of_pos_left he]; nth_rw 1 [←abs_of_pos he, ←Real.norm_eq_abs]; rw [←norm_mul,mul_sub,mul_div_cancel₀ _ he.ne'] -- name
     rw [show t^2*(Radial.jet f 2 x+t • (Radial.jet f (2+1) x)+(t^2) • (Radial.jet f (2+2) x))=Zone.eval (Radial.jet f) 4 t x by simp [Zone.eval,Finset.sum_range_succ,h.base0,h.base1];ring]
     refine hh.trans ?_; rw [show t^2*(C*_*_*t^3)= C*w^5*t^(4+1) by change t^2*(C*w^5*1*t^3)=_;ring]; gcongr
lemma amplified (W:E→F)(hW:ContDiffAt ℝ ∞ W 0)(hv:W 0=0)(a:ScriptJ F)(hp:a.B) : Pawn fun t x=> (a (t⁻¹ • W (t • x))).atK t:=by
     let w (t:ℝ)(x:E):= t⁻¹ • W (t • x); have he (c: Module.Dual ℝ F): Pawn fun t x=>c (w t x):=by
        let f:E→ℝ:= (toContinuousLinearMap c) ∘ W; have hg: f 0=0:= by unfold f;rw [comp_apply,hv,map_zero]
        have ht:= hill ((toContinuousLinearMap c).contDiff.contDiffAt.comp 0 hW) hg
        unfold w; simp_rw [map_smul, smul_eq_mul]; exact ⟨_,ht⟩
     obtain ⟨h1,h2,h3⟩:= bondX hp
     have ht:Pawn fun t (_:E)=>t:= (stay (fun _=>⟨0,1,0⟩) (ScriptJ.Xbond (Bond.keep 0) (Bond.keep 1) (Bond.keep 0))).compare ⟨1,one_pos,fun x t ht hm=>by simp [quitt,JetS.atK]⟩
     exact ((join _ h1 he).sum (ht.cash (join _ h2 he))).sum (by convert! (ht.cash ht).cash (join _ h3 he) using 1 ; funext u x;simp [pow_two,w])
end Pawn
end YM.OPE.Libra
