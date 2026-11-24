import YM.FormalBulk08.Tundra.Earn

/-!
Per-step mark budget. `e,r` unchanged separated out. No polynomial moment loss.
Thus $I$-transmission and $D$ may spend powers using ancestry or reporting units
at arbitrary contacts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {X:Type}{U:X→Type*}{τ:Time X}{R:X→Type} {E r m u D:ℕ}{η σ δ:X→ℝ}
lemma uph (p i j:ℕ){S:∀ i, Reach (R i)}{e:ℕ}{q Q:∀ i:X,R i→R i→ℝ}(hG:Gilt τ S η δ q Q)(hs:∀ i,0≤η i){Z W:∀ x:X, OrbitV (R x)}(hZ:∀ i,Fiery (Z i))(hW:∀ i,Fiery (W i)){T L:∀ x:X,U x→OrbitV (R x)}{b:∀ i,U i→ℝ}{o:∀ i,U i→ R i} (hv:j+p>0)
   (hf:orbit_access e r i j p)(hp:∀ n i k,i≤e→0<k →Totem τ S η δ (fun x=> swim (q x) (Z x) n i k) (fun x=> swim (Q x) (W x) n i k))(he:∀ i j:ℕ,precede e r i j → 0 < j → Matched τ S o η δ b (fun x p=> T x p i j) (fun x p=> L x p i j)):
   Matched τ S o η δ b (fun x u=>dipper (q x) (swim (q x) (Z x)) (T x u) p i j) (fun x u=>dipper (Q x) (swim (Q x) (W x)) (L x u) p i j):= by
   induction p using Nat.strong_induction_on generalizing i j with
   | _ p ih=>
      cases p with
      | zero=> simp_rw [dipper_first]; unfold orbit_access at hf; exact he i j (Or.resolve_right hf (by omega)) (by omega)
      | succ n=>
         simp_rw [dipper_succ]; refine Matched.amp (Matched.plus ((ih n (by omega) i _ (by omega) (prices_flow hf (by omega))).bake hs hG) (Matched.amp ?_ (Pact.coin ..))) (Pact.coin ..)
         unfold brawl Lava.reach;apply matched_sums _; intro l hl; apply matched_sums _; intro v hL;apply matched_sums _;intro w hw; rw [Finset.mem_antidiagonal] at hl hL; simp_rw [visor_eq]; apply Matched.lengthen; apply Matched.polish
         by_cases h:l.1=0
         · have hh(x:X)(n r): swim (q x) (Z x) n 0 r=0:= by by_contra ht;have hp:=(thermal (q x) (hZ _) _ _ _ ht).1;omega
           have hu(x:X)(n r):swim (Q x) (W x) n 0 r=0:= by by_contra ht;have hp:=(thermal (Q x) (hW _) _ _ _ ht).1;omega
           simp_rw [h,hh,hu,bond_void];apply mates_void
         exact Matched.bond (hp _ _ _ (by unfold orbit_access precede at *;omega) (by omega)) (ih v.2 (by omega) _ _ (by omega) (by unfold orbit_access precede at *;omega)) hG hs

variable {K:KernelChoices}{ρ:ChartRatio G} {j t:ℕ}
abbrev Det (P:Flight j t)(V:Lodge P.patch)(K:KernelChoices)(T:Tile (edgeL G) m) := jetty (coastRight _ _ _) (urn P V G K T)
def plusB (P:Flight j t)(V:Lodge P.patch)(W T:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(l e r:ℕ) := ∑ i∈ (Finset.range (l+3*e+1)).erase 0,jetty (coastRight _ _ _) (border P V W T ρ h i e r)
lemma braiser (P:Flight j t)(V:Lodge P.patch)(W T:Pot G)(ρ: ChartRatio G)(h:P.patch.Branches K G)(l e r:ℕ): braise P V W T ρ h l e r= Det P V K (T e r) + plusB P V W T ρ h l e r:= by unfold braise plusB; rw [← Finset.add_sum_erase _ _ (a:=0) (by simp)];nth_rw 1 [border,dipper_first];rfl
variable {j t:X→ℕ}{F:∀ x:X,Flight (j x) (t x)}{P:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{a:hue G}{o:∀ i:X,U i→edgeL G}{b:∀ i,U i→ℝ}
    {L V:∀ x:X,Train (j x)}{W Y:X→Pot G}{ε θ:X→ℝ≥0}{κ:Loc G 1}
variable (w:Wells τ F P H ρ a σ η δ L V W Y E)(h:Soft τ (fun i=> (η i)⁻¹))(he: ∀ i, ε i≤1)(hf: ∀ i, ε i≤(F i).L.val*θ i)
include w h he hf
lemma star_w {T S:∀ i:X,U i→Tile (edgeL G) m}(κ:Loc G 1)(ht:Lacy u τ o θ δ b T S): Lacy u τ (fun i p=>coastRight _ _ _ (chief (graded F L i) (o i p) κ)) ε δ b (fun i p=>urn (graded F L i) (P i) G K (T i p)) (fun i p=>urn (graded F V i) (P i) G K (S i p)):= by
    have hp i:0<η i:= w.pay.output i; exact freezeL (freezeL (freezeL (colder_way ht he hf) (maori_constant (Aster.Freight.river (F:=F))) h he hp w.pay.board w.dpos (fun i p=>Sum.inr κ)) (maori_constant (Freight.rising (F:=F) (U:=P))) h he hp w.pay.slots w.dpos (fun i p=>Sum.inr κ)) (w.carts.zeal w.dpos) h he hp w.pay.slots w.dpos (fun i p=>Sum.inr κ)
lemma plasters {T S:∀ i:X,U i→Pot G}(e r l:ℕ)(κ:Loc G 1)(hx:e≤E)(ht:∀ j m, precede e r j m→0<m → Lacy u τ o θ δ b (fun i p=> T i p j m) (fun i p=> S i p j m)): Lacy u τ (fun i p=> chief (graded F L i) (o i p) κ) ε δ b (fun i p=> plusB (graded F L i) (P i) (W i) (T i p) ρ (H i) l e r) (fun i p=> plusB (graded F V i) (P i) (Y i) (S i p) ρ (H i) l e r):= by
    have hW i:= (w.aV i).toVivid; have hY i:= (w.bV i).toVivid
    unfold Lacy plusB; apply matched_sums _; intro i hi; refine colds ?_
    have hp x:=w.pay.output x; let A(x:X):=BoardL G (F x).patch (P x)
    refine uph (Z:=fun i=>cola (W i) ρ (graded F L i) (P i) K) (W:=fun i=>cola (Y i) ρ (graded F V i) (P i) K) (T:=fun i p=> coves K (graded F L i) (P i) (T i p)) (L:=fun i p=>coves K (graded F V i) (P i) (S i p)) _ _ _ (classic h hp he u (Canvas.gilt (F:=F) w.pay w.carts w.dpos)) (fun x=> Nat.cast_nonneg u) (fun i=>fairy _ _ _ _ K (hW i) w.pharmacy) (fun i=> fairy _ _ _ _ K (hY i) w.pharmacy) (by have := Finset.ne_of_mem_erase hi;omega) (show orbit_access e r e r i from Or.inr ⟨rfl,rfl,Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)⟩) (fun i j k hZ hy=> pennCosts h hp he u (strict_on (F:=F) w.pay w.carts w.pharmacy w.dpos hW hY w.paid j k i (hZ.trans hx) hy)) (fun j k hk hr=> star_w w h he hf κ (ht j k hk hr))
lemma stronger {T S:∀ i:X,U i→Pot G}(e r l:ℕ)(κ:Loc G 1)(hx:e≤E)(ht:∀ j m,precede e r j m → 0<m → Lacy u τ o θ δ b (fun i p=> T i p j m) (fun i p=> S i p j m))(hu:Lacy u τ o θ δ b (fun i p=>T i p e r) (fun i p=>S i p e r)): Lacy u τ (fun i p=>chief (graded F L i) (o i p) κ) ε δ b (fun i p=>braise (graded F L i) (P i) (W i) (T i p) ρ (H i) l e r) (fun i p=>braise (graded F V i) (P i) (Y i) (S i p) ρ (H i) l e r):= by simp_rw [braiser]; exact Matched.plus (colds (star_w w h he hf κ hu)) (plasters w h he hf e r l κ hx ht)
end YM.FormalBulk08.Tundra
