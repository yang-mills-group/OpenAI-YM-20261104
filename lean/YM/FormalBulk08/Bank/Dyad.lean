import YM.FormalBulk08.Bank.Alps

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {V X Y U I : Type*} {L m n : Side}

def dye (R : Row V U) (A : Row V I) (D : Row X U) (K : Row X I) : Row (V⊕X) (U⊕I):=
   Sum.elim (fun i=> Sum.elim (R i) (A i)) (fun i=> Sum.elim (D i) (K i))
lemma fileStrip {σ Z : ℝ} {R : Row V U} {A : Row V I} {D : Row X U} {K : Row X I} (h : R.strip σ Z) (k : A.strip σ Z) (u : D.strip σ Z) (j : K.strip σ Z) : (dye R A D K).strip σ Z := by
   rintro (i|i) (a|a)
   exacts [h i a,k i a,u i a,j i a]
lemma stillborn {σ C : ℝ} (h : 0≤C) : (0:Row V X).strip σ C:=by intro i j; simp [Width,SumBudget,h]
def bifid (n : Side) (V X : Type*) := (Equiv.prodSumDistrib (Site n) V X).symm
lemma dye_spot (R : Row V U) (A : Row V I) (D : Row X U) (K : Row X I) (n : Side) (x : Tor n V⊕Tor n X) (y : Tor n U⊕Tor n I) : (dye R A D K).acts n (bifid n V X x) (bifid n U I y)=Matrix.fromBlocks (R.acts n) (A.acts n) (D.acts n) (K.acts n) x y := by cases x <;> cases y <;> rfl
lemma deadActs (V X : Type*) (n : Side) : (0:Row V X).acts n=0:=by ext; simp [Row.acts]
-- equil transport polynomials

def joust (f : V≃X) (p : Pap V) := PowerSeries.map (MvPolynomial.rename f).toRingHom p
lemma joust_level [Fintype V] [Fintype X] (f : V≃X) (p : Pap V) (b r : ℕ) : rancho (joust f p) b r=jetty f.symm (rancho p b r):=by rw [rancho,joust,coeff_map]; change marble r (MvPolynomial.rename f _)=_;rw [Shore.pebble,cores_once];rfl
lemma jetty_turn {r : ℕ} (f : V≃X) (T : Tile V r) : jetty f (jetty f.symm T)=T:= by funext; simp [jetty,Function.comp_def]
lemma infer_joust [Fintype V] [Fintype X] (f : V≃X) (p : Pap V) (b r): rancho p b r=jetty f (rancho (joust f p) b r):=by rw [joust_level,jetty_turn]

-- commuting swim gauge-agnostic. No topology used for bijections.
variable {r : ℕ} (f : V≃X) (M : V→V→ℝ) (N : X→X→ℝ) (h : ∀ i j,N (f i) (f j)=M i j)
lemma jet_length {m n} (e : m=n) (T : Tile X m) : jetty f (lengthen e T) = lengthen e (jetty f T):=by cases e; rfl
lemma jet_sand (T : Tile X r) : jetty f (sand T)=sand (jetty f T):=by funext; rfl
lemma jet_sums (P : Finset U) (T : U→Tile X r): jetty f (∑ i∈P,T i)=∑ i∈P,jetty f (T i) := by funext; simp [Finset.sum_apply,jetty]
include h
lemma dyes_stare (T : Tile X (r+1+1)) : jetty f (stare N T)= stare M (jetty f T):= by
   funext v; change (stare N T) _ = _; simp only [stare]; rw [←Equiv.tsum_eq (Equiv.prodCongr f f)]; refine tsum_congr fun x=> ?_; simp only [Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,h];simp only [Lava.shed,jetty,Fin.comp_cons]
lemma dyes_bond {m n} (T : Tile X (m+1)) (S : Tile X (n+1)): jetty f (bond N T S)=bond M (jetty f T) (jetty f S):= by
   funext v; change bond N T S _= _; simp only [bond]; rw [←Equiv.tsum_eq (Equiv.prodCongr f f)]; refine tsum_congr fun x=>?_ ; simp only [Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,h];simp only [clutch,Lava.shed,jetty,Fin.comp_cons,Function.comp_assoc]
lemma dye_swim (T : OrbitV X) (P : OrbitV V) (k : ∀ e r,P e r=jetty f (T e r)) (n b r) : jetty f (swim N T n b r)=swim M P n b r:=by
   induction n using Nat.strong_induction_on generalizing b r with
   | _ n ih=>
      cases n with
      | zero=> rw [swim_first,swim_first,k]
      | succ n=>
        rw [swim_succ,swim_succ]; change ((n+1:ℕ):ℝ)⁻¹ • (jetty f (stare N (swim N T n b (r+1+1))) + jetty f (brawl N (swim N T) (swim N T) n b r)) = _
        congr 2
        · rw [dyes_stare f M N h, ih _ (by omega)]
        unfold brawl Lava.reach; rw [jet_sums];apply Finset.sum_congr rfl; intro a ha; rw [jet_sums]; refine Finset.sum_congr rfl fun c hc=>?_;rw [jet_sums]; refine Finset.sum_congr rfl fun d hd=>?_ ; rw [Finset.mem_antidiagonal] at hc
        rw [visor_eq,visor_eq,jet_length,jet_sand,dyes_bond f M N h,ih c.1 (by omega),ih c.2 (by omega)]
end YM.FormalBulk08.Bank
