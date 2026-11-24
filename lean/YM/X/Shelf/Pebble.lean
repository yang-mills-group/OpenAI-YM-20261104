import YM.X.Reed.Oka
import YM.X.Clear.Null
/-!
# Sequences in fixed spaces carried with scalar growth. No Banach needed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Shelf
open Lattice Wilson Next.Rank Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V W:Type*}
section algebra
variable [AddCommGroup V][Module ℂ V] [AddCommGroup W][Module ℂ W]
def Badge (V:Type*) [AddCommGroup V][Module ℂ V](P: (ℕ→ℂ)→ Prop)(A:Submodule ℂ V): Submodule ℂ (ℕ→V):= Submodule.span ℂ {p| ∃ (c:ℕ→ℂ) (v:V),P c∧v∈A∧ p=fun i=> c i • v}
variable {A:Submodule ℂ V}{B:Submodule ℂ W}{P Q:(ℕ→ℂ)→ Prop}{p:ℕ→V}
lemma badged (c:ℕ→ℂ){f:V}(hp:P c)(hf:f∈A): (fun i=> c i • f)∈Badge V P A:= Submodule.subset_span ⟨c,f,hp,hf,rfl⟩
lemma ordered {B:Submodule ℂ V}(h:A≤B)(he:∀ p,P p→ Q p):Badge V P A≤Badge V Q B:= by apply Submodule.span_le.mpr; rintro _ ⟨c,v,hp,hv,rfl⟩; exact badged _ (he c hp) (h hv)
lemma moved (L: V→ₗ[ℂ] W)(hv: ∀ x∈A,L x∈ B)(h:p∈Badge V P A): (fun i=>L (p i))∈Badge W P B:= by
   induction h using Submodule.span_induction with
   | mem p h => obtain ⟨c,v,x,y,rfl⟩:=h;simp only [map_smul]; exact badged c x (hv v y)
   | zero=> simp only [Pi.zero_apply,map_zero]; exact Submodule.zero_mem _
   | add f g a b x y=> simp only [Pi.add_apply,map_add]; exact Submodule.add_mem _ x y
   | smul a i h y=> simp only [Pi.smul_apply,map_smul]; exact Submodule.smul_mem _ a y
abbrev Steady (V:Type*)[AddCommGroup V][Module ℂ V]:= Badge V Released ⊤
private lemma restore (v:V): (fun _:ℕ=>v)∈ Steady V := by rw [show (fun _:ℕ=>v)=(fun _=> (1:ℂ) • v) from by simp]; exact badged _ ⟨1,tendsto_const_nhds⟩ (by simp)
lemma stead (v:V) : (fun _:ℕ=>v)∈ Steady V:=restore v
end algebra
variable {c f:ℕ→ℂ}
include hq
lemma late (h: Vanished q c):Released c:=⟨0,Vanished.goes hq h⟩
omit hq
lemma charged (h:Released c): Charged q c:= by obtain ⟨C,hc,h⟩:= (Released.old h).exists_pos; refine Charged.of_pay (Ripe.costed (a:=C) ?_); simpa only [Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤1), mul_one] using h.bound
lemma breaths (h:Released c)(hp:Released f): Released (c*f):= by obtain ⟨a,h⟩:= h; obtain ⟨b,g⟩:=hp; exact ⟨a*b,h.mul g⟩
lemma constell (a:ℂ) : Released (fun _=>a):=⟨a,tendsto_const_nhds⟩
variable {a:ℤ}
lemma poised : Charged q (fun i=> Complex.ofReal (epsilon q i^a)):= by
   let f(i:ℕ):= Complex.ofReal (epsilon q i^a); refine ⟨-a,Ripe.eventual (B:=1) ?_⟩; refine Eventually.of_forall (fun i=> ?_); rw [Complex.norm_real,Real.norm_of_nonneg (zpow_pos (epsilon_pos q _) _|>.le),ticket,one_mul,eps_eq,inv_zpow,zpow_neg]
lemma eps_supp (h:Vanished q c) :Vanished q (fun i=>(epsilon q i)^a • c i) := h.right (show Charged q (fun i=>Complex.ofReal (epsilon q i^a)) from poised) -- real smul defeq?
end YM.PositionX.Shelf
