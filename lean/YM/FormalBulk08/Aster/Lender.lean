import YM.FormalBulk08.Aster.Toucan

/-! Pump lower supplies; pennies exponent e-1 only. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {K:KernelChoices} {X:Type} {E e r m n p:ℕ} (ρ:ChartRatio G)
variable {j t:X→ℕ}(F:∀ x:X,Flight (j x) (t x)) (U:∀ x:X,Lodge (F x).patch)(H:∀ x:X,(F x).patch.Branches K G)(D L:∀ i:X,Train (j i))
-- argument types for transport
def plum (T:X→ Pot G) (x:X) := waken (graded F D x) (U x) (T x) ρ (H x)
abbrev ham (G:Gauge)(K:KernelChoices)(i:X):= setkin G (pink K.penalty (graded F D i).land)
variable {ρ F U H D L} {τ:Time X}{σ η δ C:X→ℝ}{T M:X→ Pot G}
lemma ripeness (h:LocalRatio ρ)(hh:∀ i,4≤ t i)(he:∀ i,Story (T i) (pink K.penalty (D i)))(x:X): Story (plum ρ F U H D T x) (pink K.penalty (graded F D x).land):= creed _ _ _ _ _ (he _) (hh _) h
variable (w:Freight F U ρ K τ σ η E)(c:Canvas F U H τ D L η δ)(he:∀ x,0≤δ x) (hp:LocalRatio ρ)(ha:∀ i,Vivid (T i))(hb:∀ i,Vivid (M i))
include w c he hp ha hb
lemma plum_bet (hy:e≤ E)(hg:∀ b s,1≤s→s≤ b+2→1≤ b→precede e r b s→ Totem τ (fun _=> fame _) σ δ (fun i=> T i b s) (fun i=> M i b s))(hk:0<p)(hx: p<e)(z:Fin n):
   Totem τ (fun _=> fame _) η δ (fun i=> plum ρ F U H D T i p n) (fun i=> plum ρ F U H L M i p n):= by
    have hu':0<n:=by have :=z.isLt;omega
    simp only [plum,waken,if_neg (show p≠0 by omega),if_neg (show n≠0 by omega),coastRun]; apply totem_sums _; intro i _
    have hu k:0≤η k:=(w.output k).le; refine Totem.shore (I:=fun i=> Minor G (F i).patch (U i)) ?_ hu
    exact fares_hop hu (fun k=> fairy (T k) ρ (graded F D k) (U k) K (ha k) hp) (Canvas.gilt (F:=F) w c he) (fun k=> fairy (M k) ρ (graded F L k) (U k) K (hb k) hp) (fun b s q hz hB hT=> totem_start (F:=F) w c he ⟨0,q⟩ (by unfold precede at hT;omega) hB hz (hg b s q hz hB hT)) i p n (Or.inl (Or.inl hx)) hu'
-- main differences required? scalar0 identically 1; ok. simplify
omit ha hb
variable (hh:∀ i,4≤ t i)(hT:∀ i, Story (T i) (pink K.penalty (D i)))(hM:∀ i, Story (M i) (pink K.penalty (L i)))
   (hr:∀ i,Teller G (η i) (C i)) (hC:Soft τ C) (a:hue G)
include hT hM hh hr hC
lemma coinage (hy:e≤E)(hg:∀ b s,1≤s→ s≤ b+2→1≤ b→precede e r b s→ Totem τ (fun _=>fame _) σ δ (fun i=>T i b s) (fun i=>M i b s)) (hx:0<e):
   Priced τ δ (fun i=> scalar a (plum ρ F U H D T i)) (fun i=>scalar a (plum ρ F U H L M i)) (e-1) := by
    let W:=plum ρ F U H
    intro n hn; by_cases ht:n=0
    · subst n
      simp_rw [show ∀ i,coeff 0 (scalar a (plum ρ F U H D T i))=1 from fun i=> (sig_mat a _ (ripeness hp hh hT i) K.penalty_pos (hh i)).1,show ∀ i,coeff 0 (scalar a (plum ρ F U H L M i))=1 from fun i=> (sig_mat a _ (ripeness hp hh hM i) K.penalty_pos (hh i)).1]; apply Pact.coin
    simp only [scalar,coeff_mk];exact teller_pay a hC hr w.output (plum_bet w c he hp (fun i=>(hT i).toVivid) (fun i=>(hM i).toVivid) hy hg (by omega) (by omega) 0)
lemma pennies (hy:e≤E)(hx:0<e)(hg:∀ b s,1≤s→s≤b+2→1≤ b→precede e r b s→ Totem τ (fun _=>fame _) σ δ (fun i=>T i b s) (fun i=> M i b s))(z:Fin r):
    Totem τ (fun _=> fame _) η δ (fun i=> penny a (plum ρ F U H D T i) e r) (fun i=> penny a (plum ρ F U H L M i) e r) := by
    have ht:= coinage w c he hp hh hT hM hr hC a hy hg hx; obtain ⟨hp',h'⟩:= ht.goods (fun i=>(sig_mat a _ (ripeness hp hh hT i) K.penalty_pos (hh i)).1) (fun i=>(sig_mat a _ (ripeness hp hh hM i) K.penalty_pos (hh i)).1)
    unfold penny; apply totem_sums _; intro i hi; have H:=Finset.ne_of_mem_erase hi; have hi:=Finset.mem_range.mp (Finset.mem_of_mem_erase hi); exact (plum_bet w c he hp (fun i=>(hT i).toVivid) (fun i=>(hM i).toVivid) hy hg (by omega) hi z).amp (hp'.income h' e _ r (by omega))
omit w c he hp hT hM hh hr hC
-- full normalized formula with prior pub price.
def manure (ρ:ChartRatio G)(a:hue G)(P:Flight m n) (V:Lodge P.patch)(h:P.patch.Branches K G)(T:Pot G)(e r:ℕ): Tile (edgeL G) r:= sludge ρ P V h T e r + penny a (waken P V T ρ h) e r
-- coupled formal output
abbrev taxi (ρ:ChartRatio G)(a:hue G)(P:Flight m n)(V:Lodge P.patch)(h:P.patch.Branches K G)(T:Pot G): Pot G:= Wine.normalized a (waken P V T ρ h)
lemma route_at (P:Flight m n)(V:Lodge P.patch)(h:P.patch.Branches K G)(hp:LocalRatio ρ)(ht:4≤ n)(M: Pot G)(hh:Story M (pink K.penalty P.wing)) {σ η A C:ℝ} (hx:0<e)(z:Fin r)(he:0≤η)(hu:η ≤ P.L.val*σ)(H:Bail (fame _) σ (M e r) A)(hC:0≤C)(hs:(zealand K P V G).strip η C): taxi ρ a P V h M e r = limiter a (setkin G (pink K.penalty P.land)) (risePath P V G K (M e r)+ manure ρ a P V h M e r):= by
    have hK:= creed P V M ρ h hh ht hp; unfold taxi; rw [joining a _ hK K.penalty_pos ht hx,rose_eq ρ P V h z hx he hu H hC hs,hK.ink, add_assoc];rfl
include w c he hp hh hT hM hr hC
lemma manured (hy:e≤E)(hx:0<e)(hz:r≤e+2)(hg:∀ b s,1≤s→ s≤ b+2→1≤b→precede e r b s→ Totem τ (fun _=>fame _) σ δ (fun i=> T i b s) (fun i=> M i b s))(z:Fin r):
    Totem τ (fun _=> fame _) η δ (fun i=> manure ρ a (graded F D i) (U i) (H i) (T i) e r) (fun i=> manure ρ a (graded F L i) (U i) (H i) (M i) e r):= (soil_paid w c he hp (fun i=>(hT i).toVivid) (fun i=>(hM i).toVivid) z hy hx hz hg).plus (pennies w c he hp hh hT hM hr hC a hy hx hg z)
end YM.FormalBulk08.Aster
