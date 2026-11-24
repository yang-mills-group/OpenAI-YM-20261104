import YM.OPE.Compatible.Spa.Fen
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {u:ℝ}{a:ℕ}
-- Nakayama
structure June (x:E≃ₗ[ℝ] Jewel F)(T:E→ₗ[ℝ] E)(W:E→Prop):Prop where
    op (p q:E): W p→ W q→W (p+q)
    next(p:E): W p→ W (T p)
    film (p:E):x (T p)= τΓ F (x p)
    full (z:F):∃ p:E,W p∧ x p 0=z
lemma jewelN {x:E≃ₗ[ℝ] Jewel F}{T:E→ₗ[ℝ] E}{W:E→Prop}(h:June x T W)(p:E): W p:=by
      obtain ⟨a,ha,he⟩:= h.full (x p 0); obtain ⟨b,hb,hB⟩:= h.full (x p 1-x a 1); obtain ⟨c,hc,hC⟩:= h.full (x p 2-(x a 2+x b 1)); suffices hx:p=a+ T b+ T (T c) by rw [hx]; exact h.op _ _ (h.op _ _ ha (h.next _ hb)) (h.next _ (h.next _ hc))
      apply x.injective; rw [map_add, map_add,h.film,h.film,h.film]; funext i;fin_cases i
      · change _= x a 0+0+0; rw [he,add_zero,add_zero];rfl
      · change _= x a 1 + x b 0+0; rw [hB,add_sub_cancel,add_zero];rfl
      change _=(x a 2+x b 1)+x c 0; rw [hC,add_sub_cancel];rfl
-- Scaling sequence charges ν
lemma onset {p q f h r z:ℕ→E}(hp:Sky u a p)(hq:Sky u a q)(hx:Thick u (h-f))(hy:Thick u (r-z))(hg:Thick u (h-r))(he:Thick u (z-q))(hl:Thick u (f-p)):p=q:=by
       have hh:= Thick.sub hg hx; have hv:=Thick.sub (Thick.add hh he) hl; -- want f-p minus
       apply sub_eq_zero.mp; apply (hp.sub hq).blind; rw [show p-q=(h-r)-(h-f)+(z-q)-(f-p)+(r-z) by abel]; exact Thick.add hv hy
-- offset accelerate prove advancing profile.P.Re
lemma naryT {p q x y:E} {A:ℕ→ E →L[ℝ] E→L[ℝ] F}(h:Thick u (fun i=>A i (p-q) x))(he:Thick u (fun i=> A i q (x-y))): Thick u (fun i=> A i p x-A i q y):=by
       rw [show (fun i=> _-A i q y)=(fun i=> A i (p-q) x) + (fun i=>A i q (x-y)) from funext (fun i=>by simp only [Pi.add_apply,map_sub,_root_.sub_apply]; abel)]; exact Thick.add h he
end YM.OPE.Hark
