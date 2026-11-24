import YM.FormalBulk08.Quire.Vision
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X : Type}{G :Gauge} {K:KernelChoices}{τ:Time X}{σ η δ g:X→ℝ}{U:X→Type*}{b:∀ i,U i→ℝ}{Y:X→Type}{o:∀ i,U i→Biglot (Y i)}{P:X→Side}{m n D u E e r:ℕ}
lemma Bear.scrolls {T :∀ i:X,U i→Tile (Biglot (Y i)) m}(h:Bear τ (fun _=>fame _) o σ b T)(he:∀ i,0≤η i)(hp:∀ i, η i≤ (P i).val*σ i)(hr:Soft τ (fun i=>Real.exp (8*η i))): Bear τ (fun _=>fame _) (fun i p=>Bank.scroll (P i) _ (o i p)) η b (fun i p=>jetty (Bank.scroll (P i) (Y i)).symm (T i p)):= by
   obtain ⟨C,hC,c,H⟩:= h; refine ⟨_,hr.times hC,fun i=>mul_nonneg (Real.exp_pos _).le (c i),fun i p=>?_⟩; rw [mul_assoc]; exact rinse_bill _ _ (hp i) (he i) (Bank.scroll (P i) _ (o i p)) (by rw [Equiv.symm_apply_apply];exact H i p)
lemma Matched.scrolls {T S:∀ i:X,U i→Tile (Biglot (Y i)) m}(h: Matched τ (fun _=>fame _) o σ δ b T S)(he:∀ i,0≤η i)(hp:∀ i,η i≤ (P i).val*σ i)(hr:Soft τ (fun i=>Real.exp (8*η i))): Matched τ (fun _=>fame _) (fun i p=> Bank.scroll (P i) _ (o i p)) η δ b (fun i p=>jetty (Bank.scroll (P i) (Y i)).symm (T i p)) (fun i p=>jetty (Bank.scroll (P i) (Y i)).symm (S i p)):= ⟨h.left.scrolls he hp hr,h.right.scrolls he hp hr,h.chalk.scrolls he hp hr⟩

-- shortcuts with scale χ pulled from parent. Horizon d ignored for costing.
def Tender (τ:Time X)(o:Loc G 1)(η g:X→ℝ)(T:X→Studio D→Tile (edgeL G) r) := Bear τ (fun _=>fame _) (fun _ _=> (0,o)) η (fun i p=>g i*‖p‖) T
def Brass (τ:Time X)(o:Loc G 1)(η δ g:X→ℝ)(T S:X→Studio D→Tile (edgeL G) r):= Matched τ (fun _=>fame _) (fun _ _=>(0,o)) η δ (fun i p=>g i*‖p‖) T S
variable {j t:X→ℕ}{F:∀ x:X,Flight (j x) (t x)}{S:∀ x:X,Lodge (F x).patch}{H:∀ i,(F i).patch.Branches K G}{o:Loc G 1}
     {hL:∀ i:X,2≤(F i).L.val}{V W:∀ i:X,Train (j i)}{ρ:ChartRatio G}
lemma Bear.noble {T:∀ i:X,U i→Tile (edgeL G) m}{a:∀ i,U i→ edgeL G}(h:Bear τ (fun _=>fame _) a σ b T)(w:Aster.Freight F S ρ K τ σ η E)(p:ease τ η (fun i=> zealand K (graded F V i) (S i) G)) (o:Loc G 1) :
     Bear τ (fun _=>fame _) (fun i r=> coastRight _ _ _ (chief (graded F V i) (a i r) o)) η b (fun i p=>urn (graded F V i) (S i) G K (T i p)):= by
   have hs i:0≤η i:=(w.output i).le; exact (((Bear.scrolls (P:=fun i=>(F i).L) h hs w.coverage w.blow).gift hs (Freight.river (F:=F)) w.board (fun i r=>Sum.inr o)).gift hs (Freight.rising (F:=F) (U:=S)) w.slots (fun i r=>Sum.inr o)).gift hs p w.slots (fun i r=> Sum.inr o)
lemma Matched.noble {T Y:∀ i:X,U i→Tile (edgeL G) m}{a:∀ i,U i→ edgeL G}(h: Matched τ (fun _=>fame _) a σ δ b T Y)(w:Aster.Freight F S ρ K τ σ η E)(p:Canvas F S H τ V W η δ)(hs:∀ x,0≤δ x)(o:Loc G 1) :
     Matched τ (fun _=>fame _) (fun i r=> coastRight _ _ _ (chief (graded F V i) (a i r) o)) η δ b (fun i u=>urn (graded F V i) (S i) G K (T i u)) (fun i u=>urn (graded F W i) (S i) G K (Y i u)) := by
   have hh i:0≤η i:=(w.output i).le; exact (((Matched.scrolls (P:=fun i=>(F i).L) h hh w.coverage w.blow).gift hh (maori_constant (Freight.river (F:=F))) w.board hs (fun i r=>Sum.inr o)).gift hh (maori_constant (Freight.rising (F:=F) (U:=S))) w.slots hs (fun i r=>Sum.inr o)).gift hh (p.zeal hs) w.slots hs (fun i r=>Sum.inr o)
lemma leaner {T:X→ Anthem D G}(F:∀ i:X, Flight (j i) (t i))(V:∀ i:X, Train (j i)) (hL:∀ i:X, 2≤(F i).L.val)(he: Tender τ o σ g (fun i u=>T i u e r))(h:∀ x,0≤g x): Bear τ (fun _=>fame _) (U:=fun i:X=>Studio D× Site (F i).L) (fun _ p=> (lift p.2,o)) σ (fun i p=>g i*‖p.1‖) (fun i p=>stepsong (graded F V i) (T i) (hL i) p.1 p.2 e r):= by
   obtain ⟨C,hC,c,H⟩:=he; refine ⟨C,hC,c,fun i p=>?_⟩; exact (knight (lift p.2) o _ (H i (throughW p.2 _ (hL i) p.1))).mono (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (through_le ..) (h i)) (c i))
lemma brass_at {T Y:X→ Anthem D G}(F:∀ i:X,Flight (j i) (t i))(V W:∀ i:X,Train (j i)) (hL:∀ i:X, 2≤(F i).L.val)(he: Brass τ o σ δ g (fun i u=>T i u e r) (fun i u=>Y i u e r))(h:∀ x,0≤g x)(hp:∀ x,0≤δ x):
     Matched τ (fun _=>fame _) (U:=fun i:X=>Studio D×Site (F i).L) (fun _ p=> (lift p.2,o)) σ δ (fun i p=>g i*‖p.1‖) (fun i p=> stepsong (graded F V i) (T i) (hL i) p.1 p.2 e r) (fun i p=> stepsong (graded F W i) (Y i) (hL i) p.1 p.2 e r) := by
    refine ⟨leaner F V hL he.1 h,leaner F W hL he.2 h,?_⟩
    have hh: Tender τ o σ (fun i=>δ i*g i) (fun i p=> (T i-Y i) p e r):= by unfold Tender;simp_rw [mul_assoc];exact he.3
    simp_rw [←mul_assoc];exact leaner F V hL (T:=fun i=>T i-Y i) hh (fun x=>mul_nonneg (hp x) (h x))
end YM.FormalBulk08.Quire
