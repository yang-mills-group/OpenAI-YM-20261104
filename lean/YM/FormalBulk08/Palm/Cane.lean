import YM.FormalBulk08.Palm.Sago

/-! Move projection faithfully (not lower Wick terms). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {m d l e n j t D :ℕ}{A B η σ:ℝ}{L: Side}{o:Loc G 1}
lemma easter_less {f: Place.Potential G}(h:f∈rangeLt (Axis→G.Color) n)(hn:0<n)(x:Cover):eastern f x-f ∈ rangeLt (Axis→G.Color) (n-1):=by cases n with
   | zero=> exact False.elim ((Nat.lt_irrefl _) hn)
   | succ n=>exact band_step h _
lemma heights (o:Loc G 1)(F:Frame G d)(q:ℕ)(r:Fin n→ℕ)(hr:∀ i,0<r i)(X: Fin n→Snap G d)(hw:∀ i,throughSlot (X i) (r i))(v:Seasons)(hv:(∑ i,r i)+upper v≤ q)(hq:q≤d)(hp:d<D)(P:Flight j t)(hd:d≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(Y:Anthem D G)(hY:Clef o Y l)(hB:Bonds F o σ q e n Y 0)
   (x:Site P.L)(hL:2≤P.L.val)(hS:∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)(hs:0<σ)(h:0<η)(he: η ≤ P.L.val*σ)(hX:(linesOf P K.penalty).strip η A)(hA:0≤A) :
    slate (upmost P.L x (chair P G K) (Y (throughW x D hL (cone D v)) e n)) d n X=
      unitStep P.L^((∑ i,r i)+upper v)*slate (Y (cone D v) e n) d n X:= by
    let U i:= Place.sampled (X i); have hh i:U i∈ rangeLt (Axis→G.Color) (r i):= steady_bl _ _ (hw i)
    have ht' i:r i≤j:= (Finset.single_le_sum (f:=r) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)).trans (by omega)
    choose f hf Hf hZ using fun i=> (accepts_V K.penalty K.penalty_pos P ht (ht' i) (U i) (hh i))
    let W i:= eastern (f i) (lift x); let z:= throughW x D hL (cone D v); obtain ⟨u,hu⟩:= hS z; obtain ⟨b,hb⟩:=hS (cone D v)
    let X' := Y (cone D v) e n
    let Z:= upmost P.L x (chair P G K) (Y z e n);change slate Z _ _ _ = _
    rw [severance Z (pearl_agate (merit (chair P G K)) (jetty_agate _ (hY.fare.2.1 z e n))) (upheave _ x (grown_budget G _ hA hX) hA he h.le hu) h, severance _ (hY.fare.2.1 _ e n) hb hs, show tariffs (fun i=> assigns (Place.sampled (X i))) Z = tariffs (fun i=>assigns (W i)) (Y z e n) from occurs _ hu hs.le x h he _ hX hA U r hh f hZ]
    let F' := fun i=> assigns (W i)
    have hU i: W i∈ rangeLt (Axis→G.Color) (r i):= band_shift (hf i) _
    let N(p:Studio D):= tariffs F' (Y p e n); have hN:IsLinearMap ℝ N:=peer_role o F' hY (fun i=>shoulder (hU i)); let M: Studio D→ₗ[ℝ]ℝ:= ⟨⟨N,hN.1⟩,hN.2⟩
    change M (throughW _ _ _ (cone D v))=_
    rw [clear_note v x hL M (by omega)]; swap
    · intro i hi; obtain ⟨u,hu⟩:= hS (cone D i.val); exact shiny_zero o F e q n (by omega) i.val l W r (by omega) hU H hs hY hB hu
    let L:=P.L; let w:=unitStep L; let A(i:Fin n):= w^r i • U i
    change w^_* tariffs F' X'= _
    rw [show tariffs F' X'=tariffs (fun i=>assigns (unitStep L^r i • U i)) X' from fairing o F e q n (by omega) v l A W r hv (fun i=> Submodule.smul_mem _ _ (hh i)) (fun i=>?_ ) hr H hs hY hB hb, scale_tariffs,pow_add]; change w^_*(w^_*_)= w^_*w^_*_; rw [mul_comm (w^(∑ i,r i)) (w^(upper v)),mul_assoc]
    rw [show W i - A i= (W i-f i)+(f i-A i) by abel]; exact Submodule.add_mem _ (easter_less (hf i) (hr i) _) (Hf i)
end YM.FormalBulk08.Palm
