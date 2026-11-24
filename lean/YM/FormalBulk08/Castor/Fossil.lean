import YM.FormalBulk08.Castor.Pear
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {X:Type}{G:Gauge}{K:KernelChoices} {d e R m n j t D l r E:ℕ}{B:Frame G d}{o: Loc G 1}
variable {V:X→ Roof.Plaza B D}{T S:X→ Anthem D G}{τ:Time X}{δ σ η g p:X→ℝ}

lemma fade {T:X→ Studio D→ Tile (edgeL G) r}(ht:Tender τ o η (fun _=>1) T)(hv:Faint τ g p): Tender τ o η g (fun i x=>p i • T i x):= by have ht:=Bear.pay ht hv; unfold Tender; simp only [one_mul] at ht;exact ht
lemma kinks (e r)(h:∀ i,Court o B (V i))(hv:∀ k t, t≤e → Tender τ o η (fun _=>1) (fun i p=> V i k p t r))(he:∀ j (k:Letter B),j<e ∨ j=e∧r≤ slots B k→ Faint τ g (fun i=> coeff j (echo B (T i) k))) : Tender τ o η g (fun i p=> crease B (V i) (T i) p e r):= by
    unfold crease Tender; simp only [Kemp.launch,surf,Finset.sum_apply]; apply bear_sums _; intro k _;apply bear_sums _; intro t ht; rw [Finset.mem_antidiagonal] at ht
    by_cases hh:t.1 < e∨ t.1=e ∧ r≤ slots B k
    · exact fade (T:=fun i p=> V i k p t.2 r) (hv k t.2 (by omega)) (he _ k hh)
    simp_rw [show ∀ i p, V i k p t.2 r=0 from fun i p=> by by_contra hk; have hp:=((h i).officers k).fare.1 p t.2 r hk; unfold Yield at *;omega, smul_zero]; exact bear_void ..
lemma adhesion {W F:X→Studio D → Tile (edgeL G) r}(h:Nextpay o τ σ η p g r F W){V:X→Studio D→Tile (edgeL G) r}(hv:Tender τ o η g V) : Nextpay o τ σ η p g r F (fun i x=>W i x-V i x):= by
    obtain ⟨C,c,H,P⟩:=h; obtain ⟨A,a,b,V⟩:=hv; refine ⟨_,c.plus a,fun i=>add_nonneg (H i) (b i),fun i B hB F v=>?_⟩;apply (penn_sub (P i B hB F v) (V i v)).mono; apply le_of_eq; ring
lemma damp {K F:X→ Studio D→ Tile (edgeL G) r}(h:Nextpay o τ σ η p g r F K)(a:X→ℝ)(hp:∀ i,|a i| ≤ 1) : Nextpay o τ σ η p g r F (fun i v=>a i • K i v):= by
    obtain ⟨C,c,H,Q⟩:=h; refine ⟨_,c,H,fun i B hB F v=>?_⟩;exact ((Q i B hB F v).smul _).mono (mul_le_of_le_one_left (Q i B hB F v).1 (hp i))

variable {J U:X→ℕ}{F:∀ x:X,Flight (J x) (U x)}{L:∀ x:X,Lodge (F x).patch}{H:∀ x,(F x).patch.Branches K G}{Z:∀ i:X,Train (J i)}{W:X→Pot G}{ρ:ChartRatio G}{a:hue G}
lemma terminal (w:Wells τ F L H ρ a σ η δ Z Z W W E)(f: Payroll K B o (graded F Z) L E R D τ σ η p)(hL:∀ i,2≤(F i).L.val)(l l':ℕ)(h:∀ i,Clef o (T i) l)(hp:∀ i,Qual (T i) o E (σ i))(hx:∀ i, echo B (T i)=0) (hl:l≤ R)(hr:r≤R+E)(he:e≤ E)(hR:d≤ R)(hg:∀ i,0≤g i)(hb:∀ j k,precede e r j k → Tender τ o σ g (fun i p=> T i p j k))(hv:∀ i, Court o B (V i))(hk:∀ k:Letter B,∀ j, j≤ e →Tender τ o η (fun _=>1) (fun i p=> V i k p j r)):
    let M i:= migrates a (graded F Z i) (L i) K (W i) ρ (H i) (hL i) d l' (T i)
    Nextpay o τ σ η p g r (fun i v=>T i v e r) (fun i v=>canopy B (V i) (M i) v e r) ∧ ∀ y j,j< e ∨ j=e∧r≤Pose.slots B y → Faint τ g (fun i=>coeff j (echo B (M i) y)):= by
    intro M
    have ht(k):Faint τ g (fun i=>coeff e (echo B (T i) k)):= by simp_rw [hx, Pi.zero_apply, map_zero]; apply faint_zero
    have hh:= mill_first w hg hL d l' e r he hb; have h':Nextpay o τ σ η p g r (fun i v=>T i v e r) (fun i v=>M i v e r):= ticker f hh hb he hr h hl ht hg; have hs j k hz:= Fidelity f hh hb he hr h hl hp ht hg (by omega) j k hz; exact ⟨adhesion h' (kinks e r hv hk hs),fun i j h=>hs _ _ h⟩
end YM.FormalBulk08.Castor
