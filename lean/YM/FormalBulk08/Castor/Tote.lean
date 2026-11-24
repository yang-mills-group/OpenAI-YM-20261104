import YM.FormalBulk08.Castor.Nest
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G: Gauge}{K:KernelChoices}{I X: Type}{W: Lab G K X}{ρ:ChartRatio G}{d E R m D e r:ℕ} {B:Frame G d}{Z:Frame G m}{o:Loc G 1}{P:SectionData B}{T:SectionData Z}{H: Hol G}
-- payroll helper because residual Court lacks salary
lemma portraits {τ:Time I}{σ g:I→ℝ}{T:I→ Tilework B} {C:I→ Roof.Plaza B D} (x:Letter B){b:I→ Letter B→ℝ} (h:∀ i,Colfax (slots B) (Pose.weight B) (T i) (b i)) (hp:∀ i j y, j≤ e→ Soft τ (fun x=>coeff j (T x i y))) (hv:∀ y j k,itinerary B x e r y j k → Tender τ o σ g (fun i p=> C i y p j k)) : Tender τ o σ g (fun i p=>Clover.track B (C i) (T i) x p e r) := by
    unfold Tender Clover.track; apply bear_sums _; rintro ⟨j,n,l⟩ hj; obtain ⟨hx,he⟩:=Finset.mem_erase.mp hj; have hb : n+l=e:= Finset.mem_antidiagonal.mp (Finset.mem_product.mp he).2
    by_cases hh:l<e; · exact Bear.amp (hv j l r (Or.inl hh)) (hp j n x (by omega))
    have hl : n=0:= by omega
    subst n; obtain rfl:l=e:= by omega
    by_cases hr : itinerary B x l r j l r
    · exact Bear.amp (hv _ _ _ hr) (hp _ _ _ (Nat.zero_le _))
    have hh i (p'):tickets B (C i) (T i) x p' r (j,(0,l))=0:= by
       change coeff 0 (T i j x) • _ = (0:Tile (edgeL G) r); rw [show coeff 0 (T i j x)=0 from Classical.byContradiction fun he=>hr (ord_only ((h i).peers j x he (fun H=>hx (Prod.ext H rfl)))),zero_smul]
    simp_rw [hh]; exact bear_void ..
lemma tender_wan {τ:Time I}{σ g g': I→ℝ}{T:I→Studio D→ Tile (edgeL G) r}(h:Tender τ o σ g T)(hv:∀ i,g i≤g' i): Tender τ o σ g' T:= Bear.below h (fun i p=>mul_le_mul_of_nonneg_right (hv i) (norm_nonneg p))

variable (h:Quota B H W o D E R)(q:Quota Z H W o D E R)(u:Use W ρ E)(v:LocalRatio ρ) (a:hue G)(hg:G.Simple)(hp:P.Sound H)(hK:Bid.pop P)(ht:T.Sound H)(hb:Bid.pop T)(hk:m≤ d)(hr:d≤ R)
abbrev peelR (i:X)(N k:ℕ)(P:SectionData B)(T:SectionData Z) : Roof.Plaza Z D:= canopy B (bornY ρ W a B P h.horizon i N k) ∘ bornY ρ W a Z T q.horizon i N k
variable (C:Pin W.scrolls)
include h q u
lemma mirror_peak (y:Letter Z)(e r:ℕ): Tender ((sage C).reach (peak C)) o (fun i=>W.eagle (peak C i)) (fun _=>1) (fun i p=> peelR (ρ:=ρ) h q a i (C.N i) (C.N i) P T y p e r) := by
    let Y:= canopy B (sectionY P h.horizon) (sectionY T q.horizon y); have hx: Qual Y o e 1 := qualCan _ _ _ (fun i=> sectionQual B P _ i o e _) (sectionQual Z T _ y o e _)
    obtain ⟨B,b,V⟩:= hx e le_rfl r; refine ⟨_,soft_coin _ B,fun _=> b,fun i p=>?_⟩; simp_rw [peelR,went_top a h,went_top a q]; exact (penn_shrink (V p) ((u.cost (peak C i).toLeaf).trans (window_le ..))).mono (show _ from (by simp))
include v hg hp hK ht hb hk hr
lemma succinct :∀ i:Letter Z,∀ e r, e≤E → r≤e+slots Z i → Tender (sage C) o W.eagle (Degree targetPower) (fun x t=> peelR (ρ:=ρ) h q a x.a (C.N x.a) x.b P T i t e r):= by
    let A:=tribal (ρ:=ρ) P h a C.N (C:=C);let B':=tribal (ρ:=ρ) T q a C.N (C:=C); let U(x:Deck C):= peelR (ρ:=ρ) h q a x.a (C.N x.a) x.b P T
    let e(x:Turn C) := bornM (ρ:=ρ) (W:=W) (T:=T) a q.horizon x.a (C.N x.a) x.b
    let M(x: Turn C)(X: Anthem D G):= canopy B (A x.bed) (migrates a (graded W.liftF (W.trail C.N) x) (W.liftU x) K (Lab.instory ρ a W C.N x.ups) ρ (W.liftH x) (scooped C x) d d X)
    have hA(x:Deck C): Court o B (A x):= birth a v h hg hp hK _ _ _ x.zone x.cap; have hB(x:Deck C): Court o Z (B' x):= birth a v q hg ht hb _ _ _ x.zone x.cap
    have hU(x:Deck C)(i:Letter Z): Clef o (U x i) (slots Z i) ∧ echo B (U x i)=0:= canopy_nav (hA x) ((hB x).officers i)
    have hm (x:Turn C)(i:Letter Z): larch (U x.bed) (e x) i= smaller (W.liftF x).L m d • M x (U x.ups i) := by
       let Q:=bornM (ρ:=ρ) (T:=P) (W:=W) a h.horizon x.a (C.N x.a) x.b
       have ht' : Story (Lab.instory ρ a W C.N x.ups) _:= (genu (W.V x.a) (W.wood x.a) _ ρ a v hg x.head).toStory
       exact captured ρ a (graded W.liftF (W.trail C.N) x) (W.liftU x) (W.liftH x) (scooped C x) _ v ht' ((W.V x.a).clock.adm _) hk (A x.ups) (A x.bed) (hA _) (hA _) Q (mat_begins a v h hg hp hK _ _ _ x.zone x.head).2.symm (B' x.ups) (B' x.bed) (hB _) (hB _) _ (mat_begins a v q hg ht hb _ _ _ x.zone x.head).2.symm _
    have he(x:Turn C):=(mat_begins a v q hg ht hb _ _ _ x.zone x.head).1
    apply avenues; intro i j k hj hv ih
    let Y x:= U x i; let R:=C.N; let μ:= Turn.rad (C:=C) (1/2)
    have hP(y)(x n)(ht: itinerary Z i j k y x n): Tender (sage C) o W.eagle (Degree targetPower) (fun p t=> U p y t x n):= by
        by_cases hh:n≤ x+slots Z y
        · exact ih _ _ _ ht hh
        exact by
            unfold Tender; simp_rw [show ∀ i p,U i y p x n=0 from fun i p=>Classical.byContradiction (fun h=>by have he:=(hU i y).1.fare.1 p x n h; unfold Yield at *;omega)]; exact bear_void ..
    let kP:= slots Z i; have hq : slots Z i≤d:= (slotsFits ..).trans hk; have hh i:0≤ Dove.bump targetPower (C:=C) i := (ratioR_pos ..).le
    have hY (i:Turn C): Qual (Y i.ups) o E (W.stub i):= by
       exact qualCan _ _ _ (fun j=> qualitative h u C v hg a i.ups j) (qualitative q u C v hg a i.ups _)
    have hx: Nextpay o (Dove.tide C) W.stub W.sail μ (Dove.bump targetPower) k (fun x p=> Y x.ups p j k) (fun x p=> M x (Y x.ups) p j k):= by
       refine (terminal (grasp u C C (fun _=>le_rfl) v hg a) (payroll_from C h u C.N) (scooped C) kP d (fun x=>(hU x.ups i).1) hY (fun x=> (hU x.ups i).2) (hq.trans hr) (by omega) hj hr hh (fun j m h=> tenderLift (p:=Turn.ups) (up_age C u.liable) (hP i j m (offhand i h))) (fun x=> hA x.bed) (fun i j' hh=> tenderLift (p:=Turn.bed) (down_age C) (rooted_quote h u C v hg ‹P.Sound H› hK a hr i (le_trans hh hj) k))).1
    let l i:= smaller (W.liftF (C:=C) i).L m d
    have hv:= damp hx l (fun _=>small_le ..)
    have Hk: Tender (Dove.tide C) o W.sail (Dove.bump targetPower) (fun x p=> Clover.track Z (U x.bed) (e x) i p j k):=by
       refine portraits i he (fun i j' z hj' => ((bought q u C C (fun _=>le_rfl) v hg ht hb a (hk.trans hr) i z j' (hj'.trans hj))).left) (fun y m r he=> tender_wan (tenderLift (p:=Turn.bed) (down_age C) (hP y m r he)) (deg_out _ C targetPower_pos.le))
    apply targe (θ:=targetPower) u.liable (show targetPower < (1/2:ℝ) by unfold targetPower;norm_num) (by unfold targetPower;norm_num) _ (mirror_peak h q u a C i j k); refine nextsolve hv Hk (fun x p=> ?_ ) (fun x=> crown_weight ((W.V x.a).S.block x.b) i)
    change (l x • M x (Y x.ups)) _ _ _= _; rw [show l x • M x (Y x.ups)= larch (U x.bed) (e x) i from (hm x i).symm, employee,(he x).due]; -- `he` qualify
end YM.FormalBulk08.Castor
