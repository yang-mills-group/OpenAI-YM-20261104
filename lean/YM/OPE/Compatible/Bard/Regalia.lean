import YM.OPE.Compatible.Bard.Hurry
/-!
# Extract using alternative copy only. Actual copies allowed to be
unrelated in cross-replicated sectors (never use those modes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells
open scoped Topology BigOperators Classical
variable {X V I G' T W : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype I][DecidableEq I][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k u J:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e r:ℝ}
variable {R:Ensemble T}
    {E': T→ Site (C.S.side k p)} {a:T→G'}
    {Q: Extra.Histories.Music (C.labels.level d) C.path N p}{w:I→ℝ}
set_option quotPrecheck false
local notation "N!"=> Site (C.side J p)
local notation "T'"=> C.path
local notation "E!"=> Mix.camp C p J k
local notation "Z"=> C.path.rep N p
local notation "B"=> Z k
local notation "O"=> C.localSection d
local notation "H"=> lantern C.path r d k
local notation "ζ"=> PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d
-- only stamped profile needed. use Camp via secondary. doesn't require Harmony of secondary
omit [Fintype G'] in
lemma declare (A:Allot C)(hA:C.Makes)(hG:G.Simple)(i:I)(f:N! ↪ T)(h :∀ i j,a (f i)=a (f j))(t:T×I→ Config G (C.side N p)→ℂ)
   (U:Config G (C.side N p)→ℂ)(hU:Continuous U)(hv:Stock.Tabs.opens C.path.levels 1 J u)(hk:u<k)(hn:k ≤ N)(hf:C.ref d ≤ u)(hx:R.move∘f=hands C p J)
   (ht: Integrable (birth (ManyCopies.Names T I) (C.path.rep N p N) t) (prior G _))
   (hy:∀ v,t (f v,i)=(center C.S p (hv.1.trans (hk.le.trans hn)) 0).copy v U)
   {X : I→ Stem T G (C.S.side k p)}{c : ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{b':ℕ→ℝ}(hp:Owned (curtain I a) (C.path.rep N p k) E' R X w ((bins C k).supportExponent-3) (gust C.path N p N (birth (ManyCopies.Names T I) (C.path.rep N p N) t) k hn))(hT:Stamp (N:=N) R (C.localSection d) E' (c k) (X i)) (hP:(X i).home ∘ f= Mix.camp C p J k)
   (hw:w i=r)(hK:0<r)(hL:Club C.path C.params (C.localSection d) (PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d) (waybill C.path.levels) (C.ref d) k N p (lantern C.path r d k) A.D c b' hn) :
   (center C.S p (hv.1.trans (hk.le.trans hn)) 0).rootTest (C.beta N p) U ≤ stakes C J u/lantern C.path r d k u:=by
   let g:= f.trans (CutOrder.pairAt T i); let d' v:=(center C.S p (hv.1.trans (hk.le.trans hn)) 0).copy v U
   let Q0:= birth (ManyCopies.Names T I) (Z N) t; let P0:= gust T' N p N Q0 k hn
   obtain ⟨P,hV,hY,h'⟩:= hp.issues; have hφ(v'):(curtain I a).safe (imageM g v') :=by
       intro i hi j hj; obtain ⟨i,_,rfl⟩:=mem_image.mp hi; obtain ⟨j,_,rfl⟩:=mem_image.mp hj; exact h i j
   have hΦ:Mirror.trim g ∘ P0= Mirror.trim g ∘ P:=funext fun i=> (show _=_ from (congr_arg Poly.inject (funext fun s=> hY i _ (hφ s))))
   have hγ : t ∘ g=d':= funext hy; have hQ:Mirror.trim g ∘ Q0=birth (Bud N!) (Z N) d':= (station g (Z N) t).trans (congr_arg _ hγ)
   have hΨ : Mirror.trim g ∘ P= gust T' N p N (birth (Bud N!) (Z N) d') k hn:= hΦ.symm.trans ((narrower g ht hn).trans (congr_arg (fun Q0=>gust T' N p N Q0 k hn) hQ))
   have he:= kiosk g h'.ship.sold (fun i=>h'.way i.2); have ht':tags X ∘ g=E!:=funext (fun i=>congr_fun hP _); rw [ht',hΨ] at he
   let F0(v):=radiant (alto C.path k d) (hands C p J v) (E! v) ((c k).exponentialEntry 0 O B); let G0(v):=sunny B (c k).forced (hands C p J v) (E! v) (alto C.path k d)
   have hp'(v:N!) : (lights X ∘ g) v=F0 v ∧ (Stem.ink X (B)∘ g) v= G0 v:=by
       have he:= hT.rays (C.localSection d) (f v); rw [show (X i).home (f v)=_ from congr_fun hP v,show R.move (f v)=_ from congr_fun hx v] at he; exact he
   rw [funext (fun v=>(hp' v).1), funext (fun v=>(hp' v).2),show Stem.quota T w∘ g=fun _=>r from funext fun _=> hw] at he
   exact blot A U hA hG hv hk hn hf hK hL hU he
end YM.OPE.Arboreal.Arcade
