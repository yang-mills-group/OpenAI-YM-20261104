import YM.FormalBulk08.Aster.Grain

/-! Lex predecessor within fixed perturbative order. No assumption
mass of rank-zero vacuum, never charge its value. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Function Filter Lava Gorge Wick
open scoped Topology ENNReal BigOperators Classical
variable {X Z I : Type*} {t:Time X} {V : X→ Type*}{m n r e:ℕ} {R : ∀ x, Reach (V x)} {σ δ : X→ℝ}
variable {q M:(x:X)→V x→ V x→ℝ} {T U:(x:X)→OrbitV (V x)} (hs:∀ i,0≤σ i)(hp:∀ i,Fiery (T i))

def precede (e r j l:ℕ): Prop := j < e ∨ j=e∧ r < l
def orbit_access (n r i k j : ℕ): Prop:= precede n r i k ∨ (i=n∧k=r∧0<j)
lemma prices_flow {j i p r n l : ℕ}(h:orbit_access n r i p (j+1))(hl: p<l): orbit_access n r i l j := by unfold orbit_access precede at *; omega
include hp hs
lemma fares_hop (H:Gilt t R σ δ q M)(he:∀ i, Fiery (U i)) (hx:∀ b r',1≤r'→ r'≤b+2 → 1≤ b → precede e r b r' → Totem t R σ δ (fun i=> T i b r') (fun i=> U i b r')) (p i j:ℕ) (h:orbit_access e r i j p)(h':0<j): Totem t R σ δ (fun x=> swim (q x) (T x) p i j) (fun x=> swim (M x) (U x) p i j):=by
    induction p using Nat.strong_induction_on generalizing i j with
    | _ p ih=>
      cases p with
      | zero=>
         simp_rw [swim_first]; by_cases ha:j≤ i+2∧1≤ i
         · apply hx i j h' ha.1 ha.2; unfold orbit_access precede at *;omega
         have ht x:T x i j=0:=by by_contra ht;obtain ⟨hv,hx,hg⟩:= hp x _ _ ht; omega
         have he x:U x i j=0:=by by_contra ht;obtain ⟨hv,hx,hg⟩:=he x _ _ ht;omega
         simp_rw [ht,he];apply voids
      | succ a=>
         simp_rw [swim_succ]; refine Totem.amp (Totem.plus (totem_stare hs H ⟨0,h'⟩ (ih a (by omega) i _ (prices_flow h (by omega)) (by omega))) ?_) (Pact.coin ..)
         unfold brawl Lava.reach; apply totem_sums _;intro u hu; apply totem_sums _;intro b hb; apply totem_sums _; intro y _; simp_rw [visor_eq]; apply Totem.lengthen;apply Totem.polish
         obtain hy:=Finset.mem_antidiagonal.mp y.property; rw [Finset.mem_antidiagonal] at hu hb;
         have hT x n r: swim (q x) (T x) n 0 r=0:=by by_contra ht; have hh:= (thermal (q x) (hp x) _ _ _ ht).1; omega
         have hU x n r: swim (M x) (U x) n 0 r=0:=by by_contra ht; have hh:= (thermal (M x) (he x) _ _ _ ht).1; omega
         by_cases hC:u.1=0
         · simp_rw [hC,hT,hU,bond_void]; apply voids
         by_cases hD:u.2=0
         · simp_rw [hD,hT,hU,bond_wane];apply voids
         exact totem_bond hs H ⟨0,by omega⟩ (ih b.1 (by omega) _ _ (by unfold orbit_access precede at *;omega) (by omega)) (ih b.2 (by omega) _ _ (by unfold orbit_access precede at *;omega) (by omega))
lemma cost_hop (H:Silver t R σ q) (hx:∀ b r',1≤r'→ r'≤b+2→1≤b → precede e r b r' → Cost t R σ (fun i=>T i b r')) (p i j:ℕ)(h:orbit_access e r i j p)(h':0<j): Cost t R σ (fun x=> swim (q x) (T x) p i j):= (fares_hop hs hp (silver_gilt (δ:=fun _=>0) H) hp (fun b r' l g f z=> Totem.constant (hx b r' l g f z)) p i j h h').left
end YM.FormalBulk08.Aster
