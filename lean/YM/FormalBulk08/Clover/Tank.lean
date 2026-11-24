import YM.FormalBulk08.Clover.Eve
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type}
variable {J U:X→ℕ}{F:∀ x:X,Flight (J x) (U x)}{V:∀ x:X,Lodge (F x).patch}{H:∀ x,(F x).patch.Branches K G}{Z L:∀ i:X,Train (J i)}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {hL:∀ i,2≤(F i).L.val}{o:Loc G 1}{B:Frame G d}{W Y:X→ Pot G}{T S A Z':X→Plaza B D}{ρ:ChartRatio G}{a:hue G}
lemma brass_cr (S T:X→ Studio D→Tile (edgeL G) r)(h:Brass τ o σ δ (fun _=>1) S T): Tender τ o σ δ (fun i p=>S i p-T i p):= by simpa only [mul_one] using brass_crisp h
lemma transfer (h:E≥e)(x:Letter B) (j:ℕ)(p:Letter B)(hp:j<e ∨ j=e ∧ r≤slots B p)(hw:d≤ R)(he:r≤ e+slots B x)(w: Wells τ F V H ρ a σ η δ Z L W Y E)(c:Payroll K B o (graded F Z) V E R D τ σ η μ)(c':Payroll K B o (graded F L) V E R D τ σ η μ)(hL:∀ i,2≤(F i).L.val)(hT:∀ i,Court o B (T i))(hv:∀ i,Court o B (S i))(hx:∀ i,Qual (T i x) o E (σ i))(hz:∀ i,Qual (S i x) o E (σ i))(hy:Tender τ o σ (fun _=>1) (fun i v=>S i x v e r))(hs:∀ j m:ℕ,precede e r j m→ Brass τ o σ δ (fun _=>1) (fun i v=> T i x v j m) (fun i v=> S i x v j m)) :
     Pact τ δ (fun i=>coeff j (pTrain B ρ a (graded F Z i) (V i) (H i) (hL i) (W i) (T i) p x)) (fun i=> coeff j (pTrain B ρ a (graded F L i) (V i) (H i) (hL i) (Y i) (S i) p x)):= by
   let QZ i:= migrates a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d d (T i x); let QL i:=migrates a (graded F L i) (V i) K (Y i) ρ (H i) (hL i) d d (S i x)
   have hr : slots B x≤R:= (slotsFits ..).trans hw; have ht : r≤ R+E:=by omega
   have hA k m (h:precede e r k m):= Matched.left (hs k m h); have hB k m (h:precede e r k m):= Matched.right (hs k m h)
   have ht': Mill d r e (graded F Z) V K hL o τ η (fun _=>1) (fun i=>T i x) QZ:=mill_first w.left (fun _=>zero_le_one) hL d d e r h hA
   have hz':Mill d r e (graded F L) V K hL o τ η (fun _=>1) (fun i=>S i x) QL:= mill_first w.right (fun _=>zero_le_one) hL d d e r h hB
   have hY j k (he:precede e r j k): Tender τ o σ δ (fun i p=>(T i x-S i x) p j k) := brass_cr _ _ (hs j k he)
   have hc:Mill d r e (graded F Z) V K hL o τ η δ (fun i=>T i x-S i x) (fun i=>QZ i -QL i):= by have hd:= crisped w (fun _=>zero_le_one) hL d d e r h hs hx hz hy; simp_rw [mul_one] at hd; exact hd
   change Pact τ δ (fun i=> coeff j (echo B (QZ i) p)) (fun i=> coeff j (echo B (QL i) p))
   have hZ: Soft τ (fun i=> coeff j (echo B (QZ i) p)):= (Clover.Fidelity (K:=K) c ht' hA h ht (fun i=>(hT i).officers x) hr hx (fun i=>rent_city x i hT _) (fun _=>zero_le_one) (by omega) j p hp).pact (fun _=>le_rfl)
   have hW:Soft τ (fun i=> coeff j (echo B (QL i) p)):= (Clover.Fidelity (K:=K) c' hz' hB h ht (fun i=> (hv i).officers x) hr hz (fun i=>rent_city x i hv _) (fun _=>zero_le_one) (by omega) j p hp).pact (fun _=>le_rfl)
   refine ⟨hZ,hW,?_⟩
   have hh:= Fidelity c hc hY h ht (fun i=> ((hT i).officers x).sub ((hv i).officers x)) hr (fun i=> qual_sub (hx i) (hz i)) (fun i=>rent_gap hT hv x i e) w.dpos (by omega) j p hp
   apply hh.lower; intro z; have hp: Clef o (QL z) (Pose.slots B x):= migrate_w (P:=graded F L z) (W:=Y z) (x:=o) a (H z) (hL z) d (hv z|>.officers x) (w.bV z) (w.church z) w.pharmacy (slotsFits ..); have ho: Clef o (QZ z) (Pose.slots B x):= migrate_w (P:=graded F Z z) (W:=W z) (x:=o) a (H z) (hL z) d (hT z|>.officers x) (w.aV z) (w.church z) w.pharmacy (slotsFits ..); change |coeff j (echo B (QZ z) p)-coeff j (echo B (QL z) p)|≤ |coeff j (echo B (QZ z-QL z) p)|; rw [chalk_less B p hp.fare ho.fare,map_sub]

lemma elliptic (x:Letter B)(H':Hol G)(h:E≥e)(hp:d ≤R)(hw:d<D)(hj:∀ i,d≤J i)(hr:r≤e+slots B x)(w:Wells τ F V H ρ a σ η δ Z L W Y E)(c:Payroll K B o (graded F Z) V E R D τ σ η μ)(c':Payroll K B o (graded F L) V E R D τ σ η μ)(hL:∀ i,2≤(F i).L.val)(hT:∀ i,Court o B (T i))(hS:∀ i,Court o B (S i))(he:∀ i,A i= avenue B ρ a (graded F Z i) (V i) (H i) (hL i) (W i) (T i))(hv:∀ i, Z' i= avenue B ρ a (graded F L i) (V i) (H i) (hL i) (Y i) (S i))(hx:∀ i,Qual (T i x) o E (σ i))(hz:∀ i,Qual (S i x) o E (σ i))(hy:Tender τ o σ (fun _=>1) (fun i v=>S i x v e r))(hs:∀ j m:ℕ, precede e r j m → Brass τ o σ δ (fun _=>1) (fun i v=> T i x v j m) (fun i v=>S i x v j m))(hU:∀ y j k,itinerary B x e r y j k → Brass τ o η δ (fun _=>1) (fun i p=> A i y p j k) (fun i p=> Z' i y p j k)):
     Nextpay o τ σ η μ δ r (fun i p=> T i x p e r-S i x p e r) (fun i p=> A i x p e r - Z' i x p e r):= by
   let Q i:= migrates a (graded F Z i) (V i) K (W i) ρ (H i) (hL i) d d ∘ T i; let U i:= migrates a (graded F L i) (V i) K (Y i) ρ (H i) (hL i) d d ∘ S i; let p i:=pTrain B ρ a (graded F Z i) (V i) (H i) (hL i) (W i) (T i); let q i:= pTrain B ρ a (graded F L i) (V i) (H i) (hL i) (Y i) (S i)
   let M (i:X)(x:Letter B):=heightK (F i).L d (Pose.weight B x)
   have hf i: Colfax (Pose.slots B) (Pose.weight B) (p i) (M i) := performed _ _ _ _ _ _ _ _ _ _ H' hw (hj i) (w.church i) (w.aV i) w.pharmacy (hT i); have hg i: Colfax (Pose.slots B) (Pose.weight B) (q i) (M i):= performed _ _ _ _ _ _ _ _ _ _ H' hw (hj i) (w.church i) (w.bV i) w.pharmacy (hS i)
   have he' i:Court o B (A i) ∧ larch (A i) (p i)=Q i:= by rw [he]; exact axle _ _ _ _ _ _ _ _ _ (hT i) (w.aV i) w.pharmacy H' hw (hj i) (w.church i)
   have hv' i:Court o B (Z' i) ∧ larch (Z' i) (q i)= U i:= by rw [hv];exact axle _ _ _ _ _ _ _ _ _ (hS i) (w.bV i) w.pharmacy H' hw (hj i) (w.church i)
   let t(i:X):=T i x-S i x; let B'(i:X):=Q i x-U i x
   have hV:_ := purchased (g:=fun _=>1) (δ:=δ) x e r hf hg (fun i=> (he' i).1) (fun i=> (hv' i).1) (fun i j hz'=>Clover.transfer h x j i hz' hp hr w c c' hL hT hS hx hz hy hs) hU -- projections
   let Hx:=brass_cr _ _ hV
   have hb: Mill d r e (graded F Z) V K hL o τ η δ t B':=by have hd:= crisped w (fun _=>zero_le_one) hL d d e r h hs hx hz hy; simp_rw [mul_one] at hd; exact hd
   have hq:slots B x ≤ R:= (slotsFits ..).trans hp
   have hw :Nextpay o τ σ η μ δ r (fun i p=> t i p e r) (fun i p=> B' i p e r):= ticker c hb (fun j m hz=>brass_cr _ _ (hs j m hz)) h (by omega) (fun i=> (hT i|>.officers x).sub (hS i|>.officers x)) hq (fun i=> rent_gap hT hS x i e) w.dpos
   apply nextsolve (b:=fun i=>M i x) (T:=fun i v=>T i x v e r-S i x v e r) (S:=fun i v=> B' i v e r) hw Hx _ (fun _=>crown_weight _ _)
   intro i v; change Q i x v e r-U i x v e r= _; rw [←(he' i).2,←(hv' i).2,employee,employee,(hf i).due,(hg i).due,smul_sub];abel
end YM.FormalBulk08.Clover
