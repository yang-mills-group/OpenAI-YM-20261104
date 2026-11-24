import YM.SchemeRG11.Plate.Script
/-! First finite-stencil laws also agree with the exact orbifold Taylor scheme. -/
set_option maxRecDepth 5000
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Bark
open Lattice Function Filter Asymptotics Haze Pert First Bare Labels
open scoped Classical ContDiff Matrix.Norms.Frobenius
variable {L : Type*} [AddCommGroup L] [One L] {G : Gauge} {N : Side}
lemma mileage_append (x:Four L)(s w:Walk)(A:trunk G L): mileage x (s++w) A=mileage x s A+mileage (stop x s) w A:=by induction s generalizing x with | nil=>simp [mileage,stop] | cons d s ih=> rw [List.cons_append,mileage,ih,mileage,stop]; abel
lemma back(x:Four L)(s:Walk)(A:trunk G L): mileage (stop x s) (Lattice.reverse s) A=-(mileage x s A):=by
 induction s generalizing x with
 | nil=> simp [mileage, Lattice.reverse]
 | cons d s ih=>
   rw [show Lattice.reverse (d::s)=Lattice.reverse s++[d.rev] from by simp [Lattice.reverse],stop,mileage_append,ih, reverse_stop,mileage,mileage,mileage,add_zero]; cases d with | mk i b=>cases b <;> simp [heel,Step.rev,Step.vec,Step.used,sub_eq_add_neg]
lemma onface(x:Four L)(s:Walk)(i j:Axis)(A:trunk G L):mileage x (Bark.turn s i j) A=wideCurl A (stop x s) i j:=by
 rw [Bark.turn,mileage_append,mileage_append,stop_append,square_stop,back]
 let z:=stop x s; have he : z+step i+step j + (-(step i):Four L)=z+step j :=by abel
 have h:mileage z (square i j) A=wideCurl A z i j:=by simp only [mileage,square,Step.vec_pos,Step.vec_neg,he]; simp [heel,posDir,negDir,wideCurl, Step.used]; abel
 change _+mileage z (square i j) A+_ = _; rw [h]; abel
lemma stock (x : Four L)(j:ℕ)(A B:trunk G L): part false x j A B=wideCore G j x A:=by
 funext i k r; rw [wideCore_apply]; simp only [part,angle,Bool.false_eq_true,↓reduceIte,onface,Bare.displaced]
lemma secular(h:ℝ)(x:Four L)(j:ℕ)(A B:trunk G L): starJet false h x j A B=wideLinear G j h x A:=by
 simp only [starJet,style,wideLinear,LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,stock]
lemma tensorExpand (v : Site N)(U: Links (Per N) G.El)(h:ℝ)(x:Cover)(j:ℕ): tensorJet h (expandAt v U) x j=tensorJet h U (wrap N x+v) j:=by
 unfold tensorJet; apply congrArg ((Fintype.card Signed:ℝ)⁻¹ • ·); apply Finset.sum_congr rfl; intro s hs
 have hr: pull s 0 (expandAt v U)=expandAt (affine s⁻¹ 0 v) (pull s 0 U):=by simp [expandAt_pull,affine]
 have he: wrap N (affine s⁻¹ 0 x)+affine s⁻¹ 0 v=affine s⁻¹ 0 (wrap N x+v):=by simp [affine]
 unfold oval; rw [hr]; apply congrArg; unfold rawJet; apply congrArg; apply congrArg; funext i k r; simp only [diffU,turn_path,travel_at,he]
def absorb (v:Site N)(U:trunk G (Per N)):trunk G ℤ:=fun l=> U (wrap N l.1+v,l.2)
lemma tensorAbs(t:Bool)(v:Site N)(U:trunk G (Per N))(h:ℝ)(x:Cover)(j:ℕ): starJet t h x j (absorb v U) (absorb v U)=starJet t h (wrap N x+v) j U U:=by
 have he r: unroll (absorb v U) r= Lattice.expandAt v (unroll U r):=rfl
 simp_rw [← accord,he,tensorExpand]
abbrev tone (G:Gauge)(j:ℕ)(i:Fin (Labels.dim G j)) : Taylor G j→L[ℝ] ℂ:=Complex.ofRealCLM ∘L ((axes G j).coord i).toContinuousLinearMap
lemma folio(h:ℝ)(x:Site N)(i: Key G): ContDiff ℝ ∞ (datum h x i):=(ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Taylor G i.1) (F:=ℂ) (tone G i.1 i.2)).comp (g:=tone G i.1 i.2) ((tensorC (U:=Orb.positiveLinks) Orb.pos_mDiff h x i.1).of_le le_top)
lemma inner_line(h:ℝ)(x:Site N)(i:Labels.Key G)(A:Orb.Potential G N): iteratedDeriv 2 (fun r:ℝ=> datum h x i (r•A)) 0 = tone G i.1 i.2 (starJet true h x i.1 A.val A.val):=by
 let F r:=tensorJet h (unroll A.val r) x i.1
 let L:=tone G i.1 i.2
 let Q := starJet true h x i.1 A.val A.val
 have hw : ∀ r : ℝ, datum h x i (r • A)=L (F r):=by intro t; rfl
 simp_rw [hw]
 have he := First.iterated_clm (d:=2) (E:=Taylor G i.1) (D:=ℂ) L (0:ℝ) ((tensorC (rollsC A.val) h x i.1).of_le le_top)
 exact he.trans (congrArg (fun p:Taylor G i.1 => L p) (show iteratedDeriv 2 F 0=Q from accord true ..))
private lemma tonal {j:ℕ} (p:Taylor G j) (i:Fin (Labels.dim G j)): (((Nat.factorial 2 : ℕ) : ℝ)⁻¹) • tone G j i p= Complex.ofReal ((axes G j).coord i ((1/2:ℝ) • p)):=by -- j implicit
 have he : (((Nat.factorial 2 : ℕ) : ℝ)⁻¹)=1/2 := by norm_num [Nat.factorial,one_div]
 rw [he]; exact ((tone G j i).map_smul ..).symm
lemma issuance(h:ℝ)(x: Site N)(c:Orb.Coords G N)(i:Key G):
 PowerSeries.constantCoeff (seriesLex h x c i)=Complex.ofReal ((axes G i.1).coord i.2 (starJet false h x i.1 (Orb.expand G N c).val (Orb.expand G N c).val)) ∧ PowerSeries.coeff 1 (seriesLex h x c i)=Complex.ofReal ((axes G i.1).coord i.2 ((1/2:ℝ) • starJet true h x i.1 (Orb.expand G N c).val (Orb.expand G N c).val)):=by
 constructor; · rw [constant_lex,secular,slope_eq];rfl
 unfold seriesLex; rw [PowerSeries.coeff_mk,lineJet _ 2 _ (folio h x i)]
 exact (congrArg (fun z:ℂ=> (((Nat.factorial 2 : ℕ):ℝ)⁻¹) • z) (inner_line h x i (Orb.expand G N c))).trans (tonal _ _)
end YM.SchemeRG11.Bark
