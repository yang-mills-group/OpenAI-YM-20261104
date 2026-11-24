import YM.FormalBulk08.Vale.Down
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {K:KernelChoices}(P:Flight j t)(R:Lodge P.patch)(ρ:ChartRatio G)(W:Pot G)(h:P.patch.Branches K G)
variable (p:Side)(u:(primary P.patch K p).Choices) (a:hue G)(V:I→Pot G)(μ:I→ℕ)(L:List I)(hv:∀ i∈L,Ritual (V i) (μ i))(hP:Story W (pink K.penalty P.wing))(hs:LocalRatio ρ)(ht:4≤ t)

def tectonic := labelled P R ρ W h p u (L.map μ).sum (packV V L) - (L.map fun i=> labelled P R ρ W h p u (μ i) (V i)).prod
lemma marred {V:Type*}[Fintype V] (U S:Pap V) : rancho (U-S)= rancho U-rancho S:= by funext e r; simp only [rancho,map_sub,←canyon_eq,Pi.sub_apply]
lemma sailed {V:Type*}[Fintype V] (U S:Heat ℝ V): Lava.posting (U-S)= Lava.posting U-Lava.posting S:=by funext i j r; simp [Lava.posting, readSlice,←canyon_eq]
lemma printed :
    posting (tectonic P R ρ W h p u V μ L)= calendarQ P R W (packV V L) ρ h (L.map μ).sum p u - campfire (fun i=> calendarQ P R W (V i) ρ h (μ i) p u) L:= by unfold tectonic; rw [sailed,←campH];simp_rw [bornm]
include hv a hP hs ht
lemma rumble :
   let A:=posting (tectonic P R ρ W h p u V μ L)
   GaugeWave (L.map μ).sum A ∧ A 0=0 ∧∀ n e r, A (n+1) e r=((n+1:ℕ):ℝ)⁻¹ • (stare (GaugeR P R h p) (A n e (r+1+1))+(2:ℝ) • brawl (GaugeR P R h p) (whirl P R W ρ h p u) A n e r+(2:ℝ) • collision (GaugeR P R h p) (fun i=>calendarQ P R W (V i) ρ h (μ i) p u) L n e r):= by
   intro A; let f:=coffer W ρ P R h p u;let q:=GaugeR P R h p; let D:= (L.map μ).sum; let Z:= fun i=>sailors P R h (V i) (μ i) p; let O:=sailors P R h (packV V L) D p
   obtain ⟨s,C,hc,c,H⟩:=aone P (K:=K) G ht; have hA:= fiat P R W ρ h p u hP.toVivid hs hc c H; have hO:Young (rancho O) D:= convict_tor P R _ h (orchestra V μ L hv a).young (orchestra V μ L hv a).committees le_rfl p hc c H; have he: coeff 0 f=0:=by unfold f coffer joust;rw [coeff_map,cobalt_base,_root_.map_zero]
   obtain ⟨B,T,Q⟩:= edema f Z μ L (fun i hi=> convict_tor P R _ h (hv i hi).young (hv i hi).committees le_rfl p hc c H) q hA (fun a b=> ray_flip P R h p a b) he O (materials P R h p V L μ hv a) hO
   have hZ: ∀ i,posting (flare q f (Z i))=_:=fun i=>bornm P R ρ W h p u (μ i) (V i)
   refine ⟨B,T,fun n e r=>?_⟩; have ht:=Q n e r; rw [posting_swim _ _ he] at ht; simp_rw [hZ] at ht;exact ht
lemma output_terms :
    let M T μ := tossed P ρ h R p u (stone W _) (Kemp.banner μ T _)
    let W' := posting (tectonic P R ρ W h p u V μ L)
    ∀ e r, rancho (M (packV V L) (L.map μ).sum - (L.map fun i=> M (V i) (μ i)).prod) e r= ∑ n∈ Finset.range ((L.map μ).sum+3*e+1), jetty (coastRight _ _ _) (W' n e r):= by
   intro M W' e r
   let U:= labelled P R ρ W h p u; let J:=fun i=>U (μ i) (V i); let Q:=terrarium P R p (G:=G)
   have hY: Q (late (L.map J).prod) = (L.map fun i=>M (V i) (μ i)).prod := by
      clear W'
      induction L with
      | nil=> simp [late]
      | cons i l ih=> rw [List.map_cons,List.prod_cons,show late (J i * (l.map J).prod)=_ from (map_mul (PowerSeries.map (Polynomial.evalRingHom 1)) (J i) _),_root_.map_mul, show Q (PowerSeries.map _ _) = _ from ih (fun i ht=> hv _ (List.mem_cons_of_mem _ ht)), List.map_cons, List.prod_cons]; congr 1; exact transmitted P R ρ W h p u _ _ (hv i List.mem_cons_self) hP hs ht
   have hX: M (packV V L) (L.map μ).sum- (L.map fun i=>M (V i) (μ i)).prod=Q (late (tectonic P R ρ W h p u V μ L)):= by unfold tectonic late; rw [_root_.map_sub,_root_.map_sub]; exact congr_arg₂ (· - ·) (transmitted P R ρ W h p u _ _ (orchestra V μ L hv a) hP hs ht).symm hY.symm
   rw [hX]; exact terran_late P R p _ (rumble P R ρ W h p u a V μ L hv hP hs ht).1 e r
end YM.FormalBulk08.Vale
