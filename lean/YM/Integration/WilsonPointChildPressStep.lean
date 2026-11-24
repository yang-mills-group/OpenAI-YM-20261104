import YM.Integration.WilsonPointChildFreight

/-! The complete absolute-link contraction with one fine child retained. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPointChildPressStep
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X:Type}{E D:ℕ}
variable {ρ:ChartRatio G}{J U:X→ℕ}{F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{Z L:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g:X→ℝ}
variable {o: Loc G 1}{T S:X→Anthem D G}{W Y:X→Pot G}(w:Aster.Freight F V ρ K τ σ η E)(c:Canvas F V H τ Z L η δ)(hp: LocalRatio ρ)(hδ:∀ x, 0≤δ x)(hg:∀ i,0≤ g i)(hL:∀ i:X,2≤(F i).L.val) (hs:Soft τ (fun i=> ((F i).L.val:ℝ))) (ht:∀ i,Vivid (W i))(hy:∀ i,Vivid (Y i))(hb:∀ e≤ E,∀ m, Totem τ (fun _=>fame _) σ δ (fun i=> W i e m) (fun i=> Y i e m))

include w c hp hδ hg hs ht hy hb
theorem filed (u e r d:ℕ) (he:e≤E)
    (main:Brass τ o σ δ g (fun i p=>T i p e r) (fun i p=>S i p e r))
    (hx:∀ j m:ℕ, precede e r j m→Brass τ o σ δ g (fun i p=>T i p j m) (fun i p=>S i p j m)):
    Matched τ (fun _=>fame _) (U:=fun i:X=>Studio D×Site (F i).L) (fun _ _=>(0,o)) η δ
      (fun i p=>g i*‖p.1‖)
      (fun i p=>((F i).L.val:ℝ)^d • braise (graded F Z i) (V i) (W i)
        (stepsong (graded F Z i) (T i) (hL i) p.1 p.2) ρ (H i) u e r)
      (fun i p=>((F i).L.val:ℝ)^d • braise (graded F L i) (V i) (Y i)
        (stepsong (graded F L i) (S i) (hL i) p.1 p.2) ρ (H i) u e r):=by
   let X'(i:X):= Studio D×Site (F i).L; let A j i(p:X' i):= border (graded F Z i) (V i) (W i) (stepsong (graded F Z i) (T i) (hL i) p.1 p.2) ρ (H i) j e r
   let B j i(p:X' i):= border (graded F L i) (V i) (Y i) (stepsong (graded F L i) (S i) (hL i) p.1 p.2) ρ (H i) j e r; let R i(_p:X' i):= coastRight Cover (Minor G (F i).patch (V i)) (Loc G 1) (0,o)
   let s:=Finset.range (u+3*e+1)
   have hv j: Matched τ (fun _=>fame _) R η δ (fun i (p:X' i)=>g i*‖p.1‖) (A j) (B j):= by
       by_cases positive:j=0
       · subst j
         have hh:= (brass_at F Z L hL main hg hδ).noble w c hδ o
         simp_rw [show ∀ i (p:X' i),chief (graded F Z i) (lift p.2,o) o=(0,o) from fun _ _=>chief_h ..] at hh
         simp only [A,B,R,border,dipper_first,coves]
         exact hh
       refine concentric (Z:= fun i=>cola (W i) ρ (graded F Z i) (V i) K) (W:=fun i=>cola (Y i) ρ (graded F L i) (V i) K) (T:=fun i (p:X' i)=>coves K (graded F Z i) (V i) (stepsong (graded F Z i) (T i) (hL i) p.1 p.2)) (S:=fun i (p:X' i)=> coves K (graded F L i) (V i) (stepsong (graded F L i) (S i) (hL i) p.1 p.2)) _ _ _ (Canvas.gilt (F:=F) w c hδ) (fun i=> (w.output i).le) (fun i=>fairy _ _ _ _ K (ht i) hp) (fun i=> fairy _ _ _ _ K (hy i) hp) (show orbit_access e r e r j from Or.inr ⟨rfl,rfl,Nat.pos_of_ne_zero positive⟩) (fun i j k hz H=> strict_on (F:=F) w c hp hδ ht hy hb j k i (hz.trans he) H) (fun j k hk=>?_)
       have hh:= (brass_at F Z L hL (hx j k hk) hg hδ).noble w c hδ o; simp_rw [show ∀ i (p:X' i),chief (graded F Z i) (lift p.2,o) o=(0,o) from fun _ _=>chief_h ..] at hh; exact hh
   let wGT i(p:X' i):=g i*‖p.1‖
   have hw: Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ wGT
       (fun i p=>∑ j∈s,jetty (coastRight _ _ _) (A j i p))
       (fun i p=>∑ j∈s,jetty (coastRight _ _ _) (B j i p)):=matched_sums s (fun j _=>(hv j).jet)
   exact Matched.amp hw (Pact.constant (hs.pows d))

end YM.Integration.WilsonPointChildPressStep
