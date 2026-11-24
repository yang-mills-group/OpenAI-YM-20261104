import YM.FormalBulk08.Quire.Faro
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K: KernelChoices} {X:Type} {E m n l e r j t D :ℕ}
-- e,r unchanged vs strict (Moon). `τ` tolls separately

def icons (P:Flight j t)(ρ:ChartRatio G)(V:Lodge P.patch)(W:Pot G)(h:P.patch.Branches K G)(T:Anthem D G)(hL:2≤P.L.val)(d u e r:ℕ)(p:Studio D) : Tile (edgeL G) r:= aven P.L d • ∑ x:Site P.L, ∑ i∈(Finset.range (u+3*e+1)).erase 0,jetty (coastRight _ _ _) (border P V W (stepsong P T hL p x) ρ h i e r)
lemma quickse (P:Flight j t)(ρ: ChartRatio G)(V:Lodge P.patch)(W:Pot G)(h:P.patch.Branches K G)(T:Anthem D G)(hL:2≤P.L.val)(d u e r:ℕ)(p:Studio D) : quick P V W T ρ h hL d u p e r= blade P K V T d e r hL p+icons P ρ V W h T hL d u e r p:= by
   simp only [quick,Grail.blade,icons, Pi.smul_apply,Finset.sum_apply,← smul_add,←Finset.sum_add_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ;rw [braise,←Finset.add_sum_erase _ _ (a:=0) (by simp)]; nth_rw 1 [border, dipper_first];rfl
-- use Aster Strict supplies with tuned δ. retain Totem full vmom budget for action.
section
variable {ρ:ChartRatio G}{J U:X→ℕ}{F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{H:∀ i,(F i).patch.Branches K G}{Z L:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g:X→ℝ}
lemma soft_aven (P:X→Side)(h:Soft τ (fun i=> ((P i).val:ℝ)))(d:ℕ): Soft τ (fun i=> aven (P i) d):= by
    refine (h.pows d).below fun i=>?_ ; rw [abs_of_pos (aven_pos ..),abs_of_nonneg (by positivity)]; have ht : (1:ℝ)≤ Fintype.card (Site (P i)):= Nat.one_le_cast.mpr (Fintype.card_pos); exact mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg _) _) (inv_le_one_of_one_le₀ ht)
lemma soft_preim (P:X→Side)(h:Soft τ (fun i=> ((P i).val:ℝ))) : Soft τ (fun i=>(Fintype.card (Site (P i)):ℝ)):=by simpa [Lattice.Site,Axis] using h.pows 4
variable {o: Loc G 1}{T S:X→Anthem D G}{W Y:X→Pot G}(w:Aster.Freight F V ρ K τ σ η E)(c:Canvas F V H τ Z L η δ)(hp: LocalRatio ρ)(hδ:∀ x, 0≤δ x)(hg:∀ i,0≤ g i)(hL:∀ i:X,2≤(F i).L.val) (hs:Soft τ (fun i=> ((F i).L.val:ℝ))) (ht:∀ i,Vivid (W i))(hy:∀ i,Vivid (Y i))(hb:∀ e≤ E,∀ m, Totem τ (fun _=>fame _) σ δ (fun i=> W i e m) (fun i=> Y i e m))
include w c hp hδ ht hy hb
lemma strict_on (i j:ℕ)(k:ℕ)(hi:i≤E)(hj:1≤j): Totem τ (fun _=>fame _) η δ (fun x=>magma (graded F Z x) (V x) (W x) ρ (H x) k i j) (fun x=> magma (graded F L x) (V x) (Y x) ρ (H x) k i j):= by
   have hx x:0≤η x:=(w.output x).le
   refine fares_hop (e:=E) (r:=0) hx (fun i=> fairy (W i) ρ (graded F Z i) (V i) K (ht i) hp) (Canvas.gilt (F:=F) w c hδ) (fun i=> fairy (Y i) ρ (graded F L i) (V i) K (hy i) hp) (fun b s p hq H he=> ?_) _ i j (show orbit_access E 0 i j k from (Or.inl (by unfold precede;omega))) hj
   -- he possible b=E+1 k; need change accessibility use `Totem fares_hop` sentinel e=E and r impossible case rank j? set e=E r=0 precede implies since j≥1 included. edit
   have he:b≤ E:= by unfold precede at *;omega
   exact totem_start (F:=F) w c hδ ⟨0,p⟩ he H hq (hb b he s)
omit hp ht hy hb
include hs hL hg
lemma blade_pays (e r d)(hr:Brass τ o σ δ g (fun i p=> T i p e r) (fun i p=> S i p e r)) : Brass τ o η δ g (fun i p=> blade (graded F Z i) K (V i) (T i) d e r (hL i) p) (fun i p=> blade (graded F L i) K (V i) (S i) d e r (hL i) p):= by
   let X' (i:X):= Studio D× Site (F i).L
   let R i (p:X' i):=urn (graded F Z i) (V i) G K (stepsong (graded F Z i) (T i) (hL i) p.1 p.2 e r)
   let U' i (p:X' i):= urn (graded F L i) (V i) G K (stepsong (graded F L i) (S i) (hL i) p.1 p.2 e r)
   have hh:= (brass_at F Z L hL hr hg hδ).noble w c hδ o; simp_rw [show ∀ (i:X) (p:X' i),chief (graded F Z i) (lift p.2,o) o=(0,o) from fun _ _=>chief_h ..] at hh
   have hx: Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ (fun i (p:X' i)=>g i*‖p.1‖) (fun i p=> jetty (coastRight _ _ _) (R i p)) (fun i p=> jetty (coastRight _ _ _) (U' i p)):= hh.jet
   have hz:=m_sum_high (o:=fun _ _=>(0,o)) (b:=fun i (p:Studio D)=>g i*‖p‖) (soft_preim (fun i=>(F i).L) hs) hx
   exact hz.amp (Pact.constant (soft_aven (fun i=>(F i).L) hs _)) -- `U' i` definitional
include hp ht hy hb
lemma icon_rush (u e r d)(he:e ≤ E)(hx:∀ j m:ℕ, precede e r j m→Brass τ o σ δ g (fun i p=> T i p j m) (fun i p=> S i p j m)):
      Brass τ o η δ g (fun i p=> icons (graded F Z i) ρ (V i) (W i) (H i) (T i) (hL i) d u e r p) (fun i p=> icons (graded F L i) ρ (V i) (Y i) (H i) (S i) (hL i) d u e r p):= by
   let X'(i:X):= Studio D×Site (F i).L; let A j i(p:X' i):= border (graded F Z i) (V i) (W i) (stepsong (graded F Z i) (T i) (hL i) p.1 p.2) ρ (H i) j e r
   let B j i(p:X' i):= border (graded F L i) (V i) (Y i) (stepsong (graded F L i) (S i) (hL i) p.1 p.2) ρ (H i) j e r; let R i(_p:X' i):= coastRight Cover (Minor G (F i).patch (V i)) (Loc G 1) (0,o)
   let s:= (Finset.range (u+3*e+1)).erase 0
   have hv j (hj:j∈s): Matched τ (fun _=>fame _) R η δ (fun i (p:X' i)=>g i*‖p.1‖) (A j) (B j):= by
       refine concentric (Z:= fun i=>cola (W i) ρ (graded F Z i) (V i) K) (W:=fun i=>cola (Y i) ρ (graded F L i) (V i) K) (T:=fun i (p:X' i)=>coves K (graded F Z i) (V i) (stepsong (graded F Z i) (T i) (hL i) p.1 p.2)) (S:=fun i (p:X' i)=> coves K (graded F L i) (V i) (stepsong (graded F L i) (S i) (hL i) p.1 p.2)) _ _ _ (Canvas.gilt (F:=F) w c hδ) (fun i=> (w.output i).le) (fun i=>fairy _ _ _ _ K (ht i) hp) (fun i=> fairy _ _ _ _ K (hy i) hp) (show orbit_access e r e r j from Or.inr ⟨rfl,rfl,Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hj)⟩) (fun i j k hz H=> strict_on (F:=F) w c hp hδ ht hy hb j k i (hz.trans he) H) (fun j k hk=>?_)
       have hh:= (brass_at F Z L hL (hx j k hk) hg hδ).noble w c hδ o; simp_rw [show ∀ i (p:X' i),chief (graded F Z i) (lift p.2,o) o=(0,o) from fun _ _=>chief_h ..] at hh; exact hh
   let wGT i(p:X' i):=g i*‖p.1‖
   have hw: Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ wGT (fun i p=>∑ j∈s, jetty (coastRight _ _ _) (A j i p)) (fun i p=>∑ j∈s,jetty (coastRight _ _ _) (B j i p)):= by exact matched_sums s (fun j hj=>(hv j hj).jet)
   exact Matched.amp (m_sum_high (o:=fun _ _=>(0,o)) (b:=fun i (p:Studio D)=>g i*‖p‖) (soft_preim (fun i=>(F i).L) hs) hw) (Pact.constant (soft_aven (fun i=>(F i).L) hs _))
end
end YM.FormalBulk08.Quire
