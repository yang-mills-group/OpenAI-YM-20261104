import YM.SchemeRG11.Plate.Jet
/-! Analytic-via-Taylor invariant shape and Ward infinitesimal identities on paths. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Bark
open Lattice Function Filter Asymptotics Haze Pert Bare Labels
open scoped Classical ContDiff Matrix.Norms.Frobenius
variable {L : Type*} [AddCommGroup L] [One L] {G : Gauge}
variable (A B C : trunk G L)
variable (s : Signed)(h : ℝ)(x : Four L)(j:ℕ)
local notation "ℬ" => style
lemma impartial : part false x j A B=part false x j A A:=by funext i k r; simp only [part,angle, Bool.false_eq_true,↓reduceIte]
lemma part_add (t:Bool): part t x j (A+B) C=part t x j A C+part t x j B C:=by
 funext i k r; cases t <;> simp only [part,angle, Bool.false_eq_true,↓reduceIte,co_add,mileage_add,smul_add,Pi.add_apply,Finset.sum_add_distrib]
lemma part_smul (t:Bool)(v:ℝ) : part t x j (v • A) C=v • part t x j A C:=by
 funext i k r; cases t <;> simp only [part,angle,Bool.false_eq_true,↓reduceIte,mileage_s,co_s, Finset.smul_sum,Pi.smul_apply] <;> simp only [smul_smul,mul_left_comm,mul_comm _ v]
lemma part_add₂ : part true x j B (A+C)=part true x j B A+part true x j B C:=by funext i k r; simp only [part,angle,↓reduceIte,co_add',Pi.add_apply,smul_add, Finset.sum_add_distrib]
lemma part_smul₂ (v:ℝ): part true x j B (v • A)=v • part true x j B A:=by funext i k r; simp only [part,angle,↓reduceIte,co_s',Pi.smul_apply,Finset.smul_sum,smul_smul,mul_left_comm,mul_comm _ v]
lemma manner_add (t : Bool) : style t h x j s (A+B) C=style t h x j s A C+ style t h x j s B C:=by unfold style; rw [map_add,part_add,map_add,smul_add,map_add]
lemma manner_smul (t:Bool)(v:ℝ): style t h x j s (v • A) B=v • style t h x j s A B:=by unfold style; simp only [map_smul,part_smul]; rw [smul_comm]
lemma both_add : style true h x j s B (A+C)=style true h x j s B A+style true h x j s B C:=by unfold style; rw [map_add,part_add₂,map_add,smul_add,map_add]
lemma both_smul (v:ℝ): style true h x j s B (v • A)=v • style true h x j s B A:=by unfold style; simp only [map_smul,part_smul₂]; rw [smul_comm]
lemma star_add (t:Bool):starJet t h x j (A+B) C= starJet t h x j A C+starJet t h x j B C:=by simp only [starJet,manner_add,Finset.sum_add_distrib,smul_add]
lemma star_add₂ : starJet true h x j B (A+C)=starJet true h x j B A+starJet true h x j B C:=by simp only [starJet,both_add,Finset.sum_add_distrib,smul_add]
lemma star_s (t:Bool)(v:ℝ): starJet t h x j (v • A) B=v • starJet t h x j A B:=by unfold starJet; simp only [manner_smul, ← Finset.smul_sum]; rw [smul_comm]
lemma star_s₂ (v:ℝ):starJet true h x j B (v • A)=v • starJet true h x j B A:=by unfold starJet; simp only [both_smul, ← Finset.smul_sum]; rw [smul_comm]
lemma coins(t:Bool): starJet t h x j A B=h^(-(j+2:ℤ)) • starJet t 1 x j A B:=by
 simp only [starJet,style,one_zpow,one_smul,map_smul]
 rw [← Finset.smul_sum,smul_comm]
variable (e : Four L→G.Color)
lemma quiet : part false x j (ascent e) A=0:=by funext i k r; unfold part; simp only [angle, Bool.false_eq_true, ↓reduceIte,mile_stop, turn_stop,sub_self,smul_zero,Finset.sum_const_zero,Pi.zero_apply]
lemma part_warm (he : e x=0): part true x j (ascent e) A + part true x j A (ascent e)+part false x j (spur e A) A=0:=by
 funext i k r
 simp only [part,angle,Bool.false_eq_true,↓reduceIte,Pi.add_apply,←smul_add,← Finset.sum_add_distrib]
 simp only [test,turn_stop,he,add_zero,map_zero,smul_zero,Finset.sum_const_zero,Pi.zero_apply]
lemma whisper : style false h x j s (ascent e) A=0:=by rw [style,(operations s e A).1,quiet,map_zero,smul_zero,map_zero]
lemma sworn : starJet false h x j (ascent e) A=0:=by simp only [starJet,whisper,Finset.sum_const_zero,smul_zero]
lemma nourish (he:e x=0): ℬ true h x j s (ascent e) A + ℬ true h x j s A (ascent e)+ℬ false h x j s (spur e A) A=0:=by
 let T:=fun z=>e (affine s 0 z)
 simp only [style,(operations s e A).1,(operations s e A).2,← map_add,←smul_add]
 rw [part_warm (e:=T),map_zero,smul_zero,map_zero]
 simp [T,affine,he]
lemma heals (he:e x=0):starJet true h x j (ascent e) A+starJet true h x j A (ascent e)+starJet false h x j (spur e A) A=0:=by unfold starJet; rw [← smul_add, ← smul_add,← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; simp only [nourish A _ h x j e he,Finset.sum_const_zero,smul_zero]
lemma rotates (t:Bool): starJet t h x j (wideLink G s A) (wideLink G s A)=Taylor.turn s⁻¹.ortho (starJet t h (affine s 0 x) j A A):=by simp_rw [←accord,steering,Bare.tensor_move]; rw [First.iterated_linear (E:=Taylor G j) (D:=Taylor G j) (Taylor.turn s⁻¹.ortho) _ ((tensorC (rollsC A) ..).of_le le_top)]
lemma hues (t:Bool)(u:G.El): starJet t h x j (G.adjoint u ∘ A) (G.adjoint u ∘ A)=Taylor.paint u (starJet t h x j A A):=by
 have hg r: unroll (G.adjoint u ∘ A) r=Lattice.gauge (fun _: Four L=>u) (unroll A r):=by funext l; simp only [unroll, Function.comp_apply,← map_smul]; apply Stationary.adjoint_exp
 simp_rw [←accord,hg,Bare.tensor_gauge]; rw [First.iterated_linear (E:=Taylor G j) (D:=Taylor G j) (Taylor.paint u) _ ((tensorC (rollsC A) ..).of_le le_top)]
lemma carry_title(x u:Four L)(U:Links L G.El)(w:Walk): travel (translate u U) x w=travel U (x+u) w:=by simpa [← pull_one,affine] using travel_pull w U 1 x u
lemma bend (S:Signed)(u:Four L)(U:Links L G.El): pull S 0 (translate u U)=translate (S⁻¹.act u) (pull S 0 U):=by
 rw [←pull_one, ←pull_one,Lattice.pull_pull,Lattice.pull_pull]; simp [affine]
lemma translateJet (U:Links L G.El)(u:Four L): tensorJet h (translate u U) x j=tensorJet h U (x+u) j:=by
 unfold tensorJet; apply congrArg ((Fintype.card Signed:ℝ)⁻¹ • ·); apply Finset.sum_congr rfl; intro S _; have he:affine S⁻¹ 0 x + S⁻¹.act u = affine S⁻¹ 0 (x+u):=by simp [affine]
 simp only [oval,bend,rawJet]; apply congrArg; apply congrArg; apply congrArg; funext i k r
 simp only [diffU, turn_path, carry_title,he]
lemma turns (t:Bool)(u:Four L): starJet t h x j (fun l=> A (l.1+u,l.2)) (fun l=> A (l.1+u,l.2))=starJet t h (x+u) j A A:=by
 let V:trunk G L:=fun l=>A (l.1+u,l.2)
 have he r: unroll V r = translate u (unroll A r):= rfl
 change starJet t h x j V V= _
 simp_rw [←accord,he,translateJet]
end YM.SchemeRG11.Bark
