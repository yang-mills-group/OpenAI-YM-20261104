import YM.Integration.WilsonPointChildPressStep
import YM.FormalBulk08.Quire.Tal

/-! The original kinetic reversion on an individually addressed one-source
    step, at its actual pressed output width. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildPressIncome
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open WilsonPointChildFreight
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X:Type}{E D:ℕ}
variable {ρ:ChartRatio G}{J U:X→ℕ}{F:∀i:X,Flight (J i) (U i)} {V:∀i:X,Lodge (F i).patch}
variable {H:∀i,X→(F i).patch.Branches K G}

def step {j t:ℕ}(P:Flight j t)(ρ:ChartRatio G)(v:Lodge P.patch)(W:Pot G)
    (h:P.patch.Branches K G)(a:hue G)(T:Anthem D G)(large:2≤P.L.val)
    (d u:ℕ)(p:Studio D)(x:Site P.L):Pot G:=
  let C:=epoch a P v K W ρ h
  Wine.stamp (bookH C) (bookU C) (((P.L.val:ℝ)^d) •
    braise P v W (stepsong P T large p x) ρ h u)

def income (F:∀i:X,Flight (J i) (U i))(σ η A B:X→ℝ)(i:X):ℝ:=
  (1+A i)*(B i)^(fineWidth F η i/σ i)

variable {τ:Time X}{σ η δ:X→ℝ}{a:hue G}{o:Loc G 1}
variable {H':∀i:X,(F i).patch.Branches K G}{Z L:∀i:X,Train (J i)}{W Y:X→Pot G}

theorem original (ws:Wells τ F V H' ρ a σ η δ Z L W Y E)
    (T:X→Anthem D G)(A B:X→ℝ)(ha:∀i,0≤A i)(hb:∀i,1≤B i)
    (large:∀i:X,2≤(F i).L.val)(d u e r:ℕ)(cap:e≤E)
    (low:∀j≤e,∀m,∀i:X,∀p:Studio D,Knoxville (fame _) 0 (0,o) (T i p j m) (A i*‖p‖))
    (top:∀j≤e,∀m,∀i:X,∀p:Studio D,Knoxville (fame _) (σ i) (0,o) (T i p j m) (B i*‖p‖)):
    ∃C:X→ℝ,Soft τ C ∧ (∀i,0≤C i) ∧ ∀i:X,∀(p:Studio D)(x:Site (F i).L),
      Knoxville (fame _) (η i) (0,o)
        (step (graded F Z i) ρ (V i) (W i) (H' i) a (T i) (large i) d u p x e r)
        (C i*(income F σ η A B i*‖p‖)):=by
  let w:=ws.left
  let g:=income F σ η A B
  let ξ:=fineWidth F η
  have fine(i:X):ξ i≤σ i:=(div_le_iff₀ (show 0<((F i).L.val:ℝ) by exact_mod_cast (F i).L.property)).mpr
    (by simpa only [mul_comm] using w.pay.coverage i)
  have gn(i:X):0≤g i:=mul_nonneg (add_nonneg zero_le_one (ha i)) (Real.rpow_nonneg (zero_le_one.trans (hb i)) _)
  have entrant (j m:ℕ)(hj:j≤e):Brass τ o ξ δ g (fun i p=>T i p j m) (fun i p=>T i p j m):=by
    apply Matched.constant
    refine ⟨fun _=>1,soft_coin τ 1,fun _=>zero_le_one,fun i p=>?_⟩
    rw [one_mul]
    have s:=w.pay.input i
    have f:=charged (fame _) (0,o) (T i p j m) (div_nonneg ((lowered w.pay).input i).le s.le)
      ((div_le_one₀ s).mpr (fine i)) (hb i) (ha i) (norm_nonneg p) (low j hj m i p) (top j hj m i p)
    rwa [div_mul_cancel₀ _ s.ne'] at f
  have quiet (j:ℕ)(hj:j≤E)(m:ℕ):Totem τ (fun _=>fame _) ξ δ (fun i=>W i j m) (fun i=>W i j m):=by
    obtain ⟨C,c,h⟩:=(w.paid j hj m).left
    exact Totem.constant ⟨C,c,fun i=>(h i).shrink (fine i)⟩
  have fresh i:Fresh (epoch a (graded F Z i) (V i) K (W i) ρ (H' i)):=
    (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
  obtain ⟨HA,HB⟩:=w.weight.goods fresh fresh
  let X'(i:X):=Studio D×Site (F i).L
  let raw j (i:X)(p:X' i):= ((F i).L.val:ℝ)^d • braise (graded F Z i) (V i) (W i)
    (stepsong (graded F Z i) (T i) (large i) p.1 p.2) ρ (H' i) u j r
  have fees j (h:j≤e):Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ
      (fun i (p:X' i)=>g i*‖p.1‖) (raw j) (raw j):=
    WilsonPointChildPressStep.filed (lowered w.pay) w.carts w.pharmacy w.dpos gn large w.air
      (fun i=>(w.aV i).toVivid) (fun i=>(w.aV i).toVivid) quiet u j r d (h.trans cap)
      (entrant _ _ h) (fun k l next=>entrant _ _ (by unfold precede at next; omega))
  let issued j (i:X)(p:X' i):= let C:=epoch a (graded F Z i) (V i) K (W i) ρ (H' i)
    Wine.bill (bookH C) (bookU C) e j r • raw j i p
  have ledger:Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ (fun i (p:X' i)=>g i*‖p.1‖)
      (fun i p=>∑j∈Finset.range (e+1),issued j i p) (fun i p=>∑j∈Finset.range (e+1),issued j i p):=by
    apply matched_sums
    intro j hj
    exact Matched.amp (fees j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)) (HA.income HB _ _ r (by omega))
  obtain ⟨C,HC,pos,read⟩:=ledger.left
  exact ⟨C,HC,pos,fun i p x=>read i (p,x)⟩

end YM.Integration.WilsonPointChildPressIncome
