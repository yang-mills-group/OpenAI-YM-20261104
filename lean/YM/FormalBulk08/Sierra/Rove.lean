import YM.FormalBulk08.Tundra.Garden
/-! One conditioned insertion not engineering-weighted. Owner extension
for polymer budgets. Work with single ROOT landmark, no translation
condition on powers, preserve/infer invariance and artifacts. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{n:Side}{D m n' d u e j t:ℕ}{σ A B:ℝ}{T:Pot G}{o:edgeL G}
structure Ritual (T: Pot G)(m:ℕ): Prop where
   young:Young T m
   committees:∀ e r,Agate (T e r)
   health:∀ (x:edgeL G)(e r:ℕ),∃ σ A:ℝ,0<σ ∧ Knoxville (fame _) σ x (T e r) A
   esteem:∀ n,Rite (Kemp.banner m T n) (Kemp.banner m T n) 1 0
lemma honor (h:Ritual T m): Authorized T:= by
    intro i a e r; refine coastal i a e r T (Kemp.banner m T) ?_ (.of_forall h.esteem)
    intro v j _; obtain ⟨σ,C,hs,Hc⟩:= h.health (0,Exterior.coord 0,i) v j; simp_rw [badge T h.young h.committees le_rfl]; exact (sieve_kalm _ Hc hs.le).1
lemma ritual_cell {X:Anthem D G}(a:Loc G 1)(p:Studio D)(h:Clef a X m): Ritual (X p) m:= by
    refine ⟨h.fare.1 p, h.fare.2.1 p,fun x e r=>?_,fun n=> (solo_iff X).mp h.ward n p⟩
    obtain ⟨σ,A,hσ,-,H⟩:=h.fare.2.2 e r; exact ⟨σ,_,hσ,penn_move (H p) hσ.le⟩
lemma pledge (h:Ritual T m) (x:edgeL G)(E:ℕ):∃ σ:ℝ,0<σ ∧∀ v r,v≤E→ ∃ B:ℝ,Knoxville (fame _) σ x (T v r) B:= by
    let s:=Finset.range (E+1) ×ˢ Finset.range (m+E+1); choose σ A hσ H using fun v:ℕ×ℕ=> h.health x v.1 v.2
    obtain ⟨i,hk,Hk⟩:= Finset.exists_min_image s σ ⟨(E,m),by simp [s]⟩; refine ⟨σ i,hσ i,fun v r he=>?_⟩; by_cases hx:r≤ m+v
    · exact ⟨_,penn_shrink (H (v,r)) (Hk _ (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩))⟩
    rw [show T v r=0 from Classical.byContradiction (fun ht=>hx (h.young v r ht))]; exact ⟨_,Knox_zeros _⟩
variable (P:Flight j t)(V:Lodge P.patch)(S:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hp:Story S (pink K.penalty P.wing))(hv:LocalRatio ρ)(ht:4 ≤ t)(hT:Ritual T m)(o)
   (k:(n:Side)→(primary P.patch K n).Choices)
-- potassium complete.
include ht hp hv hT k
lemma testified (e r:ℕ):∃ η:ℝ,0<η ∧ Kalm η (chief P o o.2) (braise P V S T ρ h m e r) (fun n=>rancho (tossed P ρ h V n (k n) (stone S _) (Kemp.banner m T _)) e r):= by
   obtain ⟨θ,hθ,hf⟩:=pledge hT o e; obtain ⟨v,hv',hU⟩:=demanded_finite P S hp e; obtain ⟨s,C,hs,hC,hA⟩:=aone P (K:=K) G ht; obtain ⟨z,B,hz,hB⟩:=(gamma_ready G K P V h).1
   let κ:=min θ v; let η:=min (min s z) (P.L.val*κ);have hc:0<κ:=lt_min hθ hv';have hη:0<η:=by unfold η; positivity
   let q:ℝ:=max 0 B; have ht:=le_max_left 0 B; have H':(gamma G K P V h).strip η q:= strip_mono hB ((min_le_left ..).trans (min_le_right ..)) (le_max_right ..); have hh : (Flight.duo K.penalty P).A0.strip η C:= strip_mono hA ((min_le_left ..).trans (min_le_left ..)) le_rfl
   refine ⟨η,hη,?_⟩; unfold braise; simp_rw [truss_rite P V S T ρ h hp hv ‹4≤t› hT.young m hT.committees le_rfl]; apply kalm_many _; intro i _; apply kalm_cut
   apply budding P V S T ρ h hp hv hT.young hT.committees le_rfl k i e r hη hC hh (show η≤P.L.val *κ from min_le_right ..) ht H' o o.2
   · intro j h r; obtain ⟨C,hC⟩:=hU j h r; exact ⟨_,hC.shrink (min_le_right ..)⟩
   intro j h r; obtain ⟨C,hC⟩:= hf j r h;exact ⟨_,penn_shrink hC (min_le_left ..)⟩
include o
lemma paragon : Ritual (braise P V S T ρ h m) m:= by
   let D:=braise P V S T ρ h m;let f n:= tossed P ρ h V n (k n) (stone S _) (Kemp.banner m T _); have hf n: Young (rancho (f n)) m:= tossed_gen P V S T ρ h hp hv ht hT.young m hT.committees le_rfl n (k n)
   choose η hη H using fun e r => testified P V S ρ h hp hv ht hT (o:=o) k e r
   have he: Young D m:= Kemp.truss P V S T ρ h hp.toVivid hv hT.young m; have hh (e r):Agate (D e r):=light_agate (H e r).1 (.of_forall fun _=>marble_agate _ _)
   refine ⟨he,hh,fun x e r=>?_,fun n=>?_⟩
   · obtain ⟨v,C,hC⟩:= H e r; exact ⟨_,_,hη e r,penn_move (vents_pay v hC) (hη ..).le⟩
   have hR (x:Side): Rite (f x) (f x) 1 0:= by
       obtain ⟨v,B',hv',hB,H₀,-⟩:=colors G K.penalty K.penalty_pos P.legal
       refine tossed_ward P ρ h V x (k x) _ (stoned_main hv'.le hB.le (H₀ P.wing).1 hp.toVivid hp.ink _) hv ht (hp.civic _) 1 0 _ _ ?_
       rw [show (primary P.patch K x).ratio.embed 0=0 from (by rw [←Ratio.root_embed,map_zero])]; exact hT.esteem _
   refine verdict n 1 (P:=D) (Q:=D) (x:=chief P o o.2) (y:=chief P o o.2) hR (fun e=>m+e) (fun e=>m+e) (fun j=>.of_forall fun x i hi=> Classical.byContradiction (fun hx=> not_lt_of_ge (hf _ j _ hx) hi)) (fun j=>.of_forall fun x i hi=>Classical.byContradiction (fun hx=>not_lt_of_ge (hf _ j _ hx) hi)) (fun j r=>⟨η j r,hη j r,H j r⟩) (fun j r=>⟨η j r,hη j r,H j r⟩) (fun j r=>badge D he hh le_rfl n j r) (fun j r=>badge D he hh le_rfl n j r)
end YM.FormalBulk08.Sierra
