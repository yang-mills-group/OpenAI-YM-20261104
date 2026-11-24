import YM.X.Try.Aspect
/-!
# Splot rank-six applications. Spin-free reading of the *provisional* Y-trajectory for selected probes. No budgets assumed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Maxwell Maxwell.Free MvPolynomial Function Set Filter MeasureTheory Asymptotics
open PertExtension LatticePT Next.Rank Next.Rank.Normal
open Pert Pert.Position Pert.RawLabels Pulse Bare Ribbon
open Interval.Size Hinge Reed Stems Haze Crate Interval
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m:ℕ} {V W I:Type*} {r R:ℝ}
variable (F:Labels.Frames G)
-- halfling from Anchor
local notation "K"=> Pert.Position.E F 6
local notation "B"=> Bank F 6
local notation "T₀"=> pureBank F 6
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "L"=> Pert.Position.lower F 4 6
local notation "γ"=> YM.PositionX.par F 6
def silver (V:Bank F 6):Prop:= pulls (YM.PositionX.par F 6) V=V
include F
lemma parLower (p: K)(h:p∈L) (hg:G.Simple): γ p=p:= by rw [up_pre F (by omega)] at h; obtain ⟨u,rfl⟩:=h; rw [par_up,even_four F hg]
def halfling (F:Labels.Frames G) := LinearMap.ker (YM.PositionX.par F 6-LinearMap.id)
def positive (p: Pert.Position.E F 6) : (halfling F) := ⟨(1/2:ℂ) • (p+YM.PositionX.par F 6 p),by rw [halfling,LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,map_smul,map_add, par_cycle, add_comm]; rfl ⟩
lemma silver_cost {v:Bank F 6}(h:silver F v)(p:Fin m→ K)(i:Fin m)(hp:∀j,j≠i→p j∈L)(hg:G.Simple)(t:Test m) : v m t (Function.update p i (γ (p i)))= v m t p:= by
   have he : v m t (γ ∘ p) = v m t p := congr_arg (fun v:Bank F 6=> v m t p) h; rw [← he]; apply congr_arg (v m t); ext1 j; by_cases ht:j=i; · subst j; simp
   rw [Function.update_of_ne ht,comp_apply,parLower F (p j) (hp j ht) hg]
namespace Splot
variable (u:Splot F) {p q':Pert.Position.E F 6}{x:Bank F 6} (hg : G.Simple)
local notation "j₀"=> u.i
local notation "W₀"=> u.probes
local notation "E'"=> Function.update u.probes u.i p
include hg
lemma lit (h:silver F x): result F u x p = result F u x (γ p):=by
   have hx : result F u x (γ p)= x u.n u.test (Function.update E' j₀ (γ (E' j₀))):= by rw [Function.update_self,Function.update_idem]; rfl
   rw [hx,silver_cost _ h _ _ _ hg]; swap; intro j hj; rw [Function.update_of_ne hj]; apply u.h _ hj; rfl
lemma accepts (h:silver F x): result F u x p=result F u x (positive F p).val:= by
   have he := lit (p:=p) F u hg h; change _=result F u x ((1/2:ℂ) • (p+ _)); rw [map_smul,map_add,← he]; rw [smul_eq_mul]; ring -- smul_eq
lemma pass_S (h:silver F x)(he:γ p= -p)(b: Workroom F 6)(hb: ∀ a∈L,b a∈ L) : result F u (billM F b x) p=result F u x (b p):= by
    change passV b (x u.n u.test) E'= _; rw [pass_view,Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _),Function.update_self,Function.update_idem]; rfl
    intro j _ hp; let f:= E'; let y:= Function.update f j (b (f j)); have hu (i)(hi:i≠j₀): f i∈L:= by unfold f; rw [Function.update_of_ne hi]; exact u.h _ hi
    have hy (i)(hi:i≠ j₀): y i∈L:= by
       unfold y; by_cases hv:i=j; · subst i; rw [Function.update_self]; apply hb _ (hu _ hi)
       rw [Function.update_of_ne hv]; apply hu _ hi
    have hs:y j₀=p:= by unfold y f; rw [Function.update_of_ne hp.symm, Function.update_self];
    have ht: x u.n u.test y=0:= by
       let A:= x u.n u.test; let b:=A y; have hx: (2:ℂ) • b=0:= by
          have h':= silver_cost F h y j₀ hy hg u.test; let Q:=Function.update y j₀ p; have hh: Q=y:= by unfold Q; rw [← hs,Function.update_eq_self]; -- hrs
          rw [hs,he,MultilinearMap.map_update_neg, show update y u.i p=y from hh] at h'; change (2:ℂ) • b=0; rw [two_smul ℂ b, ← neg_eq_iff_add_eq_zero] -- name
          exact h' -- fix
       exact (smul_eq_zero.mp hx).resolve_left (by norm_num)
    exact ht
end Splot
end YM.PositionX.Tri
