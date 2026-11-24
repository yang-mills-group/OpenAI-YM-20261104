import YM.FormalBulk08.Vale.Loom
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
lemma provisioning [Fintype V](P:Heat ℝ V)(h:GaugeWave i (posting P))(e r): rancho (late P) e r=∑ j∈Finset.range (i+3*e+1),Lava.posting P j e r:= by
    rw [rancho,marbled_late];exact tsum_eq_sum (fun j k=>Classical.byContradiction fun he=>not_lt_of_ge (h j e r he) (by simp only [Finset.mem_range,not_lt] at k;omega))
lemma novel_map_prod {A B:Type*}[Monoid A][Monoid B](P:I→A)(F:A→*B)(L:List I) : F (L.map P).prod=(L.map fun i=> F (P i)).prod:= by
    induction L with
    | nil=> simp
    | cons i L ih=> simp [ih]
variable {K:KernelChoices}(P:Flight j t)(R:Lodge P.patch)(ρ:ChartRatio G)(W:Pot G)(h:P.patch.Branches K G)(p: Side)(u:(primary P.patch K p).Choices)
abbrev GaugeR:= (rayshot P R h).acts p
def labelled (i:ℕ)(V:Pot G): Heat ℝ (Tor p (BoardL G P.patch R)):= flare (GaugeR P R h p) (coffer W ρ P R h p u) (sailors P R h V i p)
lemma bornm (i:ℕ)(V: Pot G) : posting (labelled P R ρ W h p u i V) = calendarQ P R W V ρ h i p u:= by
    let T:=coffer W ρ P R h p u;have hq:coeff 0 T=0:=by unfold T coffer joust;rw [coeff_map,cobalt_base,map_zero]
    unfold labelled; rw [posting_dipper _ _ _ hq (fun x y=> ray_flip P R h p x y),posting_swim _ _ hq]; rfl
-- project post on actual fields exactly `jetty` by ring hom on ALL V

def terrarium : Pap (Tor p (BoardL G P.patch R))→+* Pap (wire G p):= ((PowerSeries.map (aftEval (Tor p (Minor G P.patch R)) (wire G p)).toRingHom).comp (PowerSeries.map (MvPolynomial.rename ((bifid p (Minor G P.patch R) (Loc G 1)).symm)).toRingHom))
lemma terran (T:Pap (Tor p (BoardL G P.patch R)))(e r): rancho (terrarium P R p T) e r= jetty (coastRight _ _ _) (rancho T e r):= by
    rw [rancho,terrarium,RingHom.comp_apply,coeff_map]; change marble r (aftEval _ _ (coeff e (joust (bifid p (Minor G P.patch R) (Loc G 1)).symm T)))=_; rw [target_port _ _, show marble r (coeff e _) = rancho _ _ _ from rfl,joust_level];rfl
lemma terran_late (T:Heat ℝ (Tor p (BoardL G P.patch R)))(h:GaugeWave i (posting T))(e r): rancho (terrarium P R p (late T)) e r=∑ j∈Finset.range (i+3*e+1),jetty (coastRight _ _ _) (posting T j e r):= by
   rw [terran, provisioning T h]; funext v; simp [Finset.sum_apply,jetty]
lemma transmitted (i:ℕ)(T: Pot G)(hV:Ritual T i)(hp: Story W (pink K.penalty P.wing))(hs:LocalRatio ρ)(ht:4≤t) :
    terrarium P R p (late (labelled P R ρ W h p u i T))= tossed P ρ h R p u (Mesa.stone W _) (Kemp.banner i T _) := by
   obtain ⟨s,C,hc,c,H⟩:=aone P (K:=K) G ht
   have hX: GaugeWave i (calendarQ P R W T ρ h i p u):= fun j e r he=> (youth_egg _ (convict_tor P R T h hV.young hV.committees le_rfl p hc c H) (fiat P R W ρ h p u hp.toVivid hs hc c H) j e r he).2
   apply banner_eq; funext e r; rw [truss_rite P R W T ρ h hp hs ht hV.young _ hV.committees le_rfl, terran_late P R p _ (show GaugeWave i (Lava.posting _) from (by rw [bornm]; exact hX)), bornm]
variable (V:I→Pot G)(L:List I)(μ:I→ℕ)(hv:∀ i∈L,Ritual (V i) (μ i))(a:hue G)
include hv a
lemma materials : sailors P R h (packV V L) (L.map μ).sum p= (L.map fun i=> sailors P R h (V i) (μ i) p).prod:= by
   dsimp only [sailors]; rw [summons V μ L hv a]; unfold joust lever Reef.seat; simp only [map_list_prod,List.map_map];rfl

end YM.FormalBulk08.Vale
