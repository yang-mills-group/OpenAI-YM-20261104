import YM.FormalBulk08.Turner.Brief
import YM.FormalBulk08.Elm.Mast
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Wick Jets Orb Matrix Filter Function PowerSeries
open Lattice RG Laurent Precision Stationary Reef Flat Bank Mesa  Lava City Wine Aster Dove Elm Quire Lotus Kemp Pose Roof Next.Free Bloch Source Source.Drops Labels
open scoped Topology ENNReal BigOperators ContDiff Classical
variable {G:Gauge}{A:Levels G}{K:KernelChoices}{c f:Side}{ρ:ChartRatio G}{i j:ℕ}
variable (P:Flight j i)(W:Pot G)(hp: Story W (pink K.penalty P.wing))(h:P.patch.Branches K G)(he: LocalRatio ρ)(ht:4≤ i)(V L:Lodge P.patch)
include hp he ht
lemma paths_out : waken P V W ρ h=waken P L W ρ h:= by
   funext j r; cases r with
   | zero=> simp [waken,sapkin]
   | succ r=>
      let Z n:=Classical.choice (chooseable n (n*P.L) (primary P.patch K n))
      have hv n: burn P V W ρ h Z n=burn P L W ρ h Z n:= by
          obtain ⟨s,C,p,B,H,-⟩:= colors G K.penalty K.penalty_pos P.legal; exact span_paths ρ P h V L (Z n) (Z n) (stone W _) he ht (stoned_main p.le B.le (H P.wing).1 hp.toVivid hp.ink _) (hp.civic _ 1 0)
      obtain ⟨a,p,H⟩:= componentwise P V W ρ h hp ht he Z j (r+1) 0
      obtain ⟨b,q,T⟩:= componentwise P L W ρ h hp ht he Z j (r+1) 0
      simp_rw [hv] at H; funext i; exact tendsto_nhds_unique (H.1 i) (T.1 i)
variable (hL:2≤ P.L.val) (a:hue G) {o: Loc G 1}{D u d:ℕ}{Y:Anthem D G}
lemma paths_mark (hz:Clef o Y u) : quick P V W Y ρ h hL d u=quick P L W Y ρ h hL d u:= by
    let k n:=Classical.choice (chooseable n (n*P.L) (primary P.patch K n)); funext x i j v
    have hP n:quickP P V W Y ρ h hL d u x n (k n)=quickP P L W Y ρ h hL d u x n (k n):= by
        unfold quickP; refine congr_arg (fun a=>_*a) (?_); apply Finset.sum_congr rfl; intro p _
        obtain ⟨s,C,q,B,H,-⟩:= colors G K.penalty K.penalty_pos P.legal; refine Turner.tossed_paths ρ P h V L (k n) (k n) (stone W _) (Kemp.banner u (stepsong P Y hL x p) _) he ht (stoned_main q.le B.le (H P.wing).1 hp.toVivid hp.ink _) (hp.civic _ 1 0) ?_
        rw [show Kemp.banner u (stepsong P Y hL x p) (n*P.patch.L)=_ from (seated (lift p) _ u _ (hz.fare.1 (Dawn.throughW p _ hL x)) (hz.fare.2.1 (Dawn.throughW p _ hL x)))]
        -- he:
        simpa using! repulp (wrap (n*P.patch.L) (lift p)) 1 _ _ ((solo_iff Y).mp hz.ward (n*P.patch.L) (Dawn.throughW p _ hL x))
    obtain ⟨_,_,H,-⟩:= brig o P V Y W ρ h hz.fare hp he hL ht le_rfl k i j d; obtain ⟨_,_,T,-⟩:=brig o P L Y W ρ h hz.fare hp he hL ht le_rfl k i j d; specialize H x; simp_rw [hP] at H; exact tendsto_nhds_unique (H.1 v) ((T x).1 v)
lemma release_larch {F: Frame G d}{Y: Roof.Plaza F D}(hp':Court o F Y) : pTrain F ρ a P V h hL W Y=pTrain F ρ a P L h hL W Y ∧avenue F ρ a P V h hL W Y=avenue F ρ a P L h hL W Y:= by
    have he':migrates a P V K W ρ h hL d d ∘ Y = migrates a P L K W ρ h hL d d ∘ Y:= by funext x; have hx:= paths_mark (d:=d) P W hp h he ht V L hL (clef_through (hp'.officers x) (slotsFits F x)); have hv:= paths_out P W hp h he ht V L; simp_rw [Function.comp_apply,migrates, hx,Roof.epoch,hv]
    unfold avenue pTrain; rw [he']; exact ⟨rfl,rfl⟩
end YM.FormalBulk08.Turner
