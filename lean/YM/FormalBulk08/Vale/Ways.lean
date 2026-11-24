import YM.FormalBulk08.Vale.Pion
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
/-! Path from heart-current of Wick crossing to cover. Ports for
metric families in kbulk. -/
variable [Fintype I](q:Biglot I→Biglot I→ ℝ)(v:(n:Side)→Tor n I→Tor n I→ℝ)
omit [Fintype I] in
structure Sweep (q:Biglot I→Biglot I→ℝ)(v:(n:Side)→Tor n I→Tor n I→ℝ) : Prop where
   lit: Wind q v
   charges:∃ σ C:ℝ,0<σ ∧ ∀ᶠ n in atTop,Grate (lake n I) σ (v n) C
   sym:∀ n i j,v n i j=v n j i
variable {q v}{o:Biglot I}(h:Sweep q v)
omit [Fintype I] in
lemma grate_moves {s B:ℝ}{n:Side}{R : Tor n I→Tor n I→ℝ}(hp: Grate (lake n I) σ R B)(he:s≤σ): Grate (lake n I) s R B:= by
    refine ⟨hp.1, fun x=>?_⟩; exact (ENNReal.tsum_le_tsum (fun _=>mul_le_mul_left (sheen_le _ he _) _)).trans (hp.2 x)
-- The wave-path estimates below use the post estimate h.
include h
lemma grazed {P:Tile (Biglot I) (r+1+1)}{U:(n:Side)→Tile (Tor n I) (r+1+1)}(w:WavePath o P U): WavePath o (stare q P) (fun n=>stare (v n) (U n)):= by
   obtain ⟨s,hs,w⟩:=w; obtain ⟨σ,C,hσ,H⟩:=h.charges; exact ⟨_,lt_min hσ hs,kalm_stare (kalm_tighter w (min_le_right σ s)) h.lit C (lt_min hσ hs) (H.mono fun n hn=>grate_moves hn (min_le_left ..))⟩
lemma path_bond {T:Tile (Biglot I) (r+1)}{K:Tile (Biglot I) (m+1)}{U:(n:Side)→Tile (Tor n I) (r+1)}{V:(n:Side)→ Tile (Tor n I) (m+1)}(w:∃ s:ℝ,0<s ∧ Kith s T U)(hp:WavePath o K V): WavePath o (bond q T K) (fun n=> bond (v n) (U n) (V n)):= by
   obtain ⟨s,hS,w,c,p⟩:=w; obtain ⟨z,hZ,Q⟩:=hp; obtain ⟨u,C,hu,H⟩:=h.charges; let k:=min u (min s z);have hk:0<k:=lt_min hu (lt_min hS hZ);have hT: Kith k T U:=⟨w,c,p.mono fun i hv=>hv.shrink ((min_le_right ..).trans (min_le_left ..))⟩
   exact ⟨k,hk,kalm_bond hT (kalm_tighter Q ((min_le_right ..).trans (min_le_right ..))) h.lit C hk (H.mono fun n hn=>grate_moves hn (min_le_left ..)) h.sym⟩
lemma path_jost {P Q: Waves (Biglot I)}{T U:(n:Side)→Waves (Tor n I)}(hp:∀ i j r,0<r → ∃ s:ℝ,0<s ∧ Kith s (P i j r) (fun n=> T n i j r))(hP:∀ i j r,WavePath o (Q i j r) (fun n=> U n i j r))(j e r): WavePath o (brawl q P Q j e r) (fun n=>brawl (v n) (T n) (U n) j e r):= by
   unfold brawl Lava.reach;refine wave_many _ fun i _=> wave_many _ fun j _=>wave_many _ fun a _=>?_; simp_rw [visor_eq]; exact WavePath.candor (path_bond h (hp _ _ (a.val.1+1) (by omega)) (hP _ _ (a.val.2+1))) _
lemma waveSpan {P:Waves (Biglot I)}{Q:J→ Waves (Biglot I)}{T:(n:Side)→Waves (Tor n I)}{U:J→(n:Side)→ Waves (Tor n I)} (s:List J)(hp:∀ i j r,WavePath o (P i j r) (fun n=> T n i j r))(he:∀ i∈s,∀ j k r,WavePath o (Q i j k r) (fun n=> U i n j k r))(j e r):
   WavePath o (scatter q P Q s j e r) (fun n=> scatter (v n) (T n) (fun i=> U i n) s j e r):=by
    induction s generalizing j e r with
    | nil=>exact wave_empty o r
    | cons t s ih=>
      have ht i hi:=he i (List.mem_cons_of_mem t hi)
      exact WavePath.plus (deployed j e r (fun m n k=> path_jost h (P:=P) (T:=T) (fun i j r _=>by obtain ⟨s,hs,Q⟩:=hp i j r; exact ⟨s,hs,Q.charges hs.le⟩) (he t List.mem_cons_self) m n k) (cuffs s ht)) (deployed (T:=fun n=>scatter (v n) _ _ s) j e r (he t List.mem_cons_self) (ih ht))
lemma waveCollision {P:J→Waves (Biglot I)}{T:J→(n:Side)→Waves (Tor n I)}(s:List J)(p:∀ i∈s,∀ j k r, WavePath o (P i j k r) (fun n=> T i n j k r))(j e r): WavePath o (collision q P s j e r) (fun n=> collision (v n) (fun i=>T i n) s j e r):= by
   induction s generalizing j e r with
   | nil=> exact wave_empty o r
   | cons i s ih=> have hp j hj:=p j (List.mem_cons_of_mem _ hj); exact (waveSpan h s (p i List.mem_cons_self) hp j e r).plus (deployed (T:=fun n=>collision (v n) _ s) j e r (p i List.mem_cons_self) (ih hp))
end YM.FormalBulk08.Vale
