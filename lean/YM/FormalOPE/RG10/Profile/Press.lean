import YM.FormalOPE.RG10.Profile.Fleece
import YM.FormalOPE.RG10.Position.Fields
/-! # The fenced *real* response and finite mesh vacuum/unit laws
From the previously constructed graph/Gaussian system of WilsonX, not vanilla evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
    Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
    InversionTop LatticePT Lattice Grid FlatFeed RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{n d:ℕ}
local notation "Ω" => PertExtension.Physical.Profile

def task {J:Type*} (t:Test n)(z:Fin n→J) : Mark J PertExtension.Physical.Profile.n := ⟨⟨n,t⟩,z⟩

variable (P : Plan F)(q:ℕ+)(m j:ℕ)
local notation "T" => offsets q
local notation "ε" => epsilon q m
local notation "e" => LatticePT.side q m

/-- node budget in isolation not estimated here. **No** multiplying averages of separate fields
in the ordinary moment; all membranes evaluated at one translated suite of positions. -/
abbrev mesh (u:Fin n→Deck F d) (x:T n m) (z:Native q m) :=
   (feed (G:=G) (side_even q m)).step (vertices G e) (∏ i, membrane P.H P.source P.sound P.chosen P.liftOff (Deck.token F d (u i)) (x i + z) ε)

def nodes (u:Fin n→Deck F d) (x:T n m) := ((origins q m).card:ℝ)⁻¹ * ∑ z∈origins q m, (coeff j (mesh P q m u x z)).re

variable (t:Test n) (u: Fin n→ Deck F d)
theorem bill : coeff j (P.begins q m d (task t u)) = ∑ x : T n m, (t (Grid.sample q m x)).re * nodes P q m j u x := by
 have hc : (InversionTop.into (P.begins q m d (task t u)))=
     ∑ x:T n m,∑ z∈origins q m, C ((Complex.ofRealHom (((origins q m).card:ℝ)⁻¹ * (t (Grid.sample q m x)).re))) * mesh P q m u x z := by
      have hu := coordinate P.H P.source P.sound P.chosen P.liftOff (Deck.token F d ∘ u) q m (fun z=> Complex.re (t (points z))); apply hu.trans; apply sum_congr (by congr 1;apply Subsingleton.elim); intro x _; apply sum_congr rfl; intro z _; rfl
 have he:= congr_arg (fun f:Series=>(coeff j f).re) hc
 simp_rw [into_coeff, map_sum, coeff_C_mul,Complex.re_sum,Complex.ofRealHom_eq_coe,Complex.re_ofReal_mul,Complex.ofReal_re] at he -- names
 rw [he]; apply sum_congr rfl; intro i _; simp_rw [nodes,mul_sum]; apply sum_congr rfl; intro p _; ring

lemma singular (x : T (n+1) m) : nodes P q m j (Fin.cons (Deck.start F d) u) x= ε^4 * nodes P q m j u (Fin.tail x):= by
 have hh (z:Native q m) : mesh P q m (Fin.cons (Deck.start F d) u) x z = C (↑(ε^4):ℂ) * mesh P q m u (Fin.tail x) z := by
   unfold mesh; rw [Fin.prod_univ_succ]; simp_rw [Fin.cons_zero,Fin.cons_succ]; rw [show Deck.token F _ (Deck.start F d)=Deck.token F 0 (Deck.start F 0) from rfl, membrane_unit _ _ _ _ _ P.certified,FlatFeed.step_external]; rfl
   exact (curtain (side_even ..) P.H P.source P.sound P.chosen P.liftOff _ (fun i:Fin n=> x i.succ+z) _).1
 unfold nodes; simp_rw [hh,coeff_C_mul,Complex.re_ofReal_mul,← mul_sum]; ring

lemma dark (u:Fin 0→Deck F d) (x:T 0 m) : nodes P q m j u x = coeff j (1:fps):= by
 simp_rw [nodes,mesh,Fintype.prod_empty, step_one,sum_const,nsmul_eq_mul]
 have ht : ((origins q m).card:ℝ)≠0:= Nat.cast_ne_zero.mpr (origin_pos .. |>.ne'); field_simp; cases j <;> simp
end YM.FormalOPE.RG10.Profile
