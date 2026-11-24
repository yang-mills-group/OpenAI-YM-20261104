import YM.X.Local.Greet
/-!
# Twist mark at tilted moment. root costs. Reliable (limit) only, no analytic-in-cutoff required.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding CellsInt
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d:ℕ}{G:Gauge}{R r:ℝ}
local notation "e"=>epsilon q
variable (A: Okay G k) (φ:Floor R) (x:E4) (P:Word G)
include hq
lemma domain_fee (w:Cover)(hr:R≥0): Visa q R 0 (k+1:ℕ) (fun _ z=> phase A (z+w)):= by
   apply (show Visa q R 0 (((k+1-0:ℕ)):ℤ) (fun i z=> jumped (n:=0) Fin.elim0 (reach (0:E4) (windP (A-rightCur k A).val.val)) (pace true z+w)) from burst_result (P:=fun _=>_) hq true hr (Nat.zero_le _) Fin.elim0 0 w ⟨_,tendsto_const_nhds⟩ (fun i=> windP_sym (A-rightCur k A).val)) -- valC typo
lemma eta_cost (j:Axis)(hr:R≥0) : Visa q R 0 (k+1:ℕ) (fun _ z=> eta (phase A) (z,j)):= by exact Visa.smult (1/2:ℝ) (Visa.add (domain_fee hq A (step j) hr) (by have he:= domain_fee hq A 0 hr; simpa only [add_zero] using he : Visa q R 0 (k+1:ℕ) (fun _ z=> phase A z)))
omit hq
lemma sun_grade (x:Cover)(i j:Axis)(k:G.ColorIndex) : sun x i j k∈Reed.grads G 1:= by
    refine (cloud_ann _).mpr (fun A h=> ?_); rw [sun_at]; change (stepValue (raising j A) i x-stepValue (raising i A) j x) k=0; have he(i j:Axis): stepValue (raising i A) j=0:=h (fun _:Fin 1=>j) i; rw [he,he,sub_self];rfl
lemma fresh_sun (a l:Axis)(k:G.ColorIndex): (fun (_:ℕ)(z:Cover)=> glyph (com (sun (z-step a) a l k)))= Clove.fresh true (sun (0-step a) a l k):= by
    funext i z; unfold Clove.fresh pace; rw [if_pos rfl]; congr 2; unfold sun; simp only [Stems.arc,map_add,map_sub,leads_single,pointB, ← add_assoc]; simp [sub_eq_add_neg] -- orientation
variable (a l: Axis)(b:G.ColorIndex)
-- theta glyph price. terms missed linearly along ℝ→ℂ conversion, ∗normalized∗ by length power
include hq φ
lemma fresh_eta : Jar true G q R 1 (fun i z=> e i ^(k+1) • glyph (str (phase A) ((z,l),b))):= by
    let p(j:G.ColorIndex) : Fan G:= Finsupp.single ((0,l),j) 1; let P(j:G.ColorIndex): G.Color→ₗ[ℝ] ℝ:= (EuclideanSpace.proj b).toLinearMap ∘ₗ G.ad (tan j); let V(j:G.ColorIndex)(z:Cover):= P j (eta (phase A) (z,l)); let c(j:G.ColorIndex)(i:ℕ)(z:Cover):=e i^(k+1)*V j z; let B(i:G.ColorIndex):Mist ℂ:=fun j z=> ↑(c i j z)
    have hp(t i:ℕ)(j:G.ColorIndex)(z:Cover) : Finsupp.single ((z,l),j) (V j z)=V j z • leadsL z (p j):= by unfold p; rw [leads_single,pointB,add_zero,Finsupp.smul_single,smul_eq_mul,mul_one]; -- eta parser
    have hv(z:Cover)(i:ℕ): θRow (phase A) ((z,l),b)= ∑ j:G.ColorIndex, V j z • leadsL z (p j):= by unfold θRow; exact Finset.sum_congr rfl (fun j _=> hp 0 i j z)
    let tUp(j):= glass (B j) * Clove.fresh true (p j); have he(i:ℕ)(z:Cover): e i ^(k+1) • glyph (str (phase A) ((z,l),b))= (∑ j:G.ColorIndex,tUp j) i z:= by
       unfold str; rw [hv z i]; rw [com_text]; unfold blade; simp_rw [map_sum,map_smul,Finset.smul_sum, Finset.sum_apply]; refine Finset.sum_congr rfl (fun j _=> ?_); unfold tUp; rw [glass₁, smul_smul]; simp only [Clove.fresh,pace,↓reduceIte,com_text]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) ..
    rw [show (fun i z=>_)=(∑ j:G.ColorIndex,tUp j) from funext (fun i:ℕ=>funext (he i))]; refine Jar.fin _ (fun j _=>?_); refine jar_glass true (n:=0) ?_ (Jar.fume (k:=0) _ (by rw [grade0]; simp));
    have hq': Visa q R 0 ((k+1:ℕ):ℤ) (fun i z=> V j z):= (eta_cost hq A l φ.positive.le).mapL ((P j).toContinuousLinearMap)
    have ht := Visa.asPow (c:=((k+1:ℕ):ℤ)) hq'; simp_rw [zpow_natCast] at ht; apply Visa.com (show Visa q R 0 (-((0:ℕ):ℤ)) (c j) from ?_); exact Visa.stretch hq ht φ.positive.le (by omega) (by omega)
lemma step_L : Jar true G q R 3 (fun i z=> e i^(k+1) • stepCloud (phase A) a z):= by
    let F(l:Axis)(b:G.ColorIndex):Deck G:=fun i z=> glyph (com (sun (z-step a) a l b))*(e i^(k+1) • glyph (str (phase A) ((z,l),b)))
    have he (i:ℕ)(z:Cover): e i^(k+1) • stepCloud (phase A) a z= (∑ l:Axis,∑ b:G.ColorIndex,F l b) i z:= by unfold stepCloud; simp_rw [Finset.sum_apply,Finset.smul_sum, ← mul_smul_comm];rfl
    rw [show (fun i z=>_ • _)= ∑ l:Axis,∑ b:G.ColorIndex,F l b from funext (fun i=> funext (he i))]; apply Jar.fin;intro l _; apply Jar.fin;intro b _; have h₁ : Jar true G q R 2 (fun (_:ℕ)(z:Cover)=> glyph (com (sun (z-step a) a l b))):= by rw [fresh_sun]; exact Jar.fume _ (sun_grade (0-step a) a l b)
    exact h₁.plus (fresh_eta hq A φ l b)
end YM.PositionX.Crystal
