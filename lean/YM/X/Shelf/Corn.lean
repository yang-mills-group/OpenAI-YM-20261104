import YM.X.Chili.Larder
import YM.X.Shelf.Steep
/-!
# flat program precision at FO. Self ∗exact leading Curly mark = Queried book up to superflat poly coefficients, horizontal throughout∗.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Shelf
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m d :ℕ}{G:Gauge}{R:ℝ} {P:ℕ→ Curly G}
local notation "Fℕ"=>(atTop:Filter ℕ)
abbrev CakeH (G:Gauge) := verse (Reed.Horizontal G) 0
def gruel (b:Bool)(P:ℕ→Curly G): Deck G:= fun i=> floatP b (P i) i
variable (b:Bool)
include hq
lemma late_visa (hr:R≥0){a:ℕ→ℂ}(h:Vanished q a) : Visa q R 0 (-(d:ℤ)) (Once a):= by
   have hw := Visa.once a (a:=(d:ℤ)) (R:=R) (late hq (eps_supp h)); exact hw.stretch hq hr (by omega) (by omega)
lemma jar_late (hr:R≥0) {T:Submodule ℂ (Curly G)}(h:P∈ Badge (Curly G) (Vanished q) T): Jar b G q R d (gruel b P):= by
   induction h using Submodule.span_induction with
   | mem f h=> obtain ⟨x,t,h,he,rfl⟩:=h; rw [show gruel b (fun i=>x i • t)=glass (Once x)*floatP b t from (by unfold gruel; simp_rw [map_smul];exact (glass₁ ..).symm)]; exact jar_glass b (late_visa (d:=d) hq hr h) (Jar.venue b (S:=⊤) (p:=t) (n:=0) (by rw [verse_top]; simp))
   | zero=> rw [show gruel b (0:ℕ→ Curly G)=0 from by ext1 i; rw [gruel,Pi.zero_apply,map_zero]]; exact Jar.zero _
   | add a c _ _ ih ig=> unfold gruel; simp only [Pi.add_apply,map_add]; exact ih.add ig
   | smul a v _ ih=> unfold gruel; simp only [Pi.smul_apply, map_smul];exact ih.scale a
lemma jar_safe (h:P∈Steady (Curly G)) : Jar b G q R 0 (gruel b P):= by
   induction h using Submodule.span_induction with
   | mem f h=> obtain ⟨x,t,h,he,rfl⟩:=h; rw [show gruel b (fun i=>x i • t)=glass (Once x)*floatP b t from (by unfold gruel; simp_rw [map_smul];exact (glass₁ ..).symm)]; refine jar_glass b (n:=0) ?_ (Jar.venue b (S:=⊤) (p:=t) (n:=0) (by rw [verse_top]; simp)); simp only [Nat.cast_zero,neg_zero]; exact Visa.once x (by simp_all only [neg_zero,zpow_zero,one_smul])
   | zero=> rw [show gruel b (0:ℕ→ Curly G)=0 from by ext1 i; rw [gruel,Pi.zero_apply,map_zero]]; exact Jar.zero _
   | add a c _ _ ih ig=> unfold gruel; simp only [Pi.add_apply,map_add]; exact ih.add ig
   | smul a v _ ih=> unfold gruel; simp only [Pi.smul_apply, map_smul];exact ih.scale a
local notation "Qu"=>fun i:ℕ=> flow G (side q i)
lemma local_jar (p:Curly G) : (fun i=>milk (Qu i) p)∈ Steady (Curly G):= by
   apply always (Q:=Qu); intro i j; simp_rw [rτ,tau]; by_cases hp:i.2=j.2∧i.1.2=j.1.2; · simp_rw [if_pos hp,Braid.cane, ← map_sub]; let z:=i.1.1-j.1.1; refine ⟨↑(Pert.Cellular.coverLine z),Complex.continuous_ofReal.continuousAt.tendsto.comp ?_⟩; exact stem_tends (paths hq) [] z
   simp_rw [if_neg hp,Complex.ofReal_zero];exact constell 0
lemma self_ration (p:Word G): (fun i=>milk (Qu i) (bookMark p 0)-looking p)∈ Badge (Curly G) (Vanished q) (CakeH G):= by
    let X:= (covarianceSymbol G); let C:=fun i:ℕ=>via (G:=G) sale (0:Site (side q i)); let t:=baseMark p; rw [base_book]; apply Eq.mp ?_ (moved (B:=CakeH G) Stems.loom.toLinearMap (fun i _=> press_loom i) (milk_slow hq X C (actual_self hq) t)); congr 1; funext i; change Stems.loom (_-_) = milk _ (loom _) - loom _; rw [map_sub]; unfold loom; rw [prepared]; rfl

lemma self_ping (p:Word G) (hr:R≥0) : Jar false G q R p.d (fun i _=> milk (Qu i) (bookMark p 0)):= by
    have ht:= jar_late hq false hr (self_ration hq p) (d:=p.d); unfold gruel at ht; simp_rw [float_false] at ht; let F:Deck G:=fun i _=> milk (Qu i) (bookMark p 0); change Jar _ _ _ _ _ F; have he:= Jar.venue (q:=q) (R:=R) false (press_word p); rw [float_false] at he; exact (sub_add_cancel F (fun _ _=> looking p)) ▸ Jar.add ht he
end YM.PositionX.Shelf
