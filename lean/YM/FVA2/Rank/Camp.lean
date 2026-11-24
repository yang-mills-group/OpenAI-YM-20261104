import YM.FVA2.Position.Flight
import YM.FVA2.Rank.Mon
/-! # Dimensional continuation and slot reflection

Commute at coordinate level with the germ, angular hypotheses and heat kernels.
See `peak` for the simultaneous cost/regularity aspect (the stated `Sync`). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue
open Function Set Filter Finset MeasureTheory
open MS MS.Heat MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Landau.Detect
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Dock MS.Train MS.Pearl
open _root_.YM.MS.Shine MS.Color
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n k:ℕ}{G:Gauge}
variable {X Y:Rack G m}{A B F: Mob G}{f:ℂ→Mob G}{U:Rip G} {b:Bool} {r q:ℤ}
-- alias to avoid collisions `flip`
abbrev hue (G:Gauge): Mob G→ₗ[ℂ] Mob G where
 toFun f m:= (Hue.flip _) (f m)
 map_add' a b:= funext fun i=> map_add _ (a i) (b i)
 map_smul' l b:= funext fun i=> map_smul _ l (b i)
local notation "Φ"=> hue G
lemma spark (w:Legs (Shore G m)) : Φ F m w= σ w.length * F m w:=rfl
lemma curl (h:Sturdy b F): Sturdy b (Φ F) := by
 refine ⟨fun m X hX=>?_,fun {i j} he w=>?_⟩
 · change (flagS X G).beam (Hue.flip _ _) = _; rw [Hue.beam,h.turn m X hX]; rfl
 rw [spark,spark,h.grows,Arts.lift,List.length_map]
lemma speed {z:UScale J}{f:J→Mob G}{a:J→ℝ}(h:fell z a f): fell z a (fun i=> hue G (f i)) := by
 intro m E _ _ _ w; unfold fieldVal; simp_rw [spark,sail_len]; exact (h m E w).L (ContinuousLinearMap.mul ℝ ℂ (σ w.length))
lemma turn (h: Form0 b F): Form0 b (Φ F):= ⟨speed h.price, curl h.token⟩
lemma hv {D:Set ℂ}(h:Hol D f): Hol D (fun i=>Φ (f i)):= by refine ⟨fun c R hX hY=> speed (h.price c R hX hY),fun m l c hc=> ?_⟩; simp_rw [spark]; exact (h.top m _ c hc).const_mul _
lemma peak (h: Sync b f): Sync b (fun i=>Φ (f i)):= ⟨ ⟨h.eye.price.elim fun u ⟨hu,hg⟩=> ⟨u,hu,speed hg⟩, hv h.eye.sky⟩, fun i hi=> curl (h.vote i hi) ⟩
lemma spinC (A:Rack G m)(a: Ridge G m) (h:Pass a A (Px m)): Hue.flip _ (Ccy a A (Px m))=Ccy a (Hue.flip _ A) (Px m):= by
 let V:=ink ( Landau.parity (A:=Arts.L m) (C:=G.ColorIndex) ) (SectorP m);
 rw [ ← black (p:= Landau.parity), ← black (p:= Landau.parity) ]; -- check type inference
 exact Pilot.leadC V (MeasurePreserving.id ..) MeasurableEmbedding.id (port a) A h
lemma shOcean (h: RockB U b)(hp: Form0 b F)(i:ℂ)(hi:i∈Town): Φ (ocean i U F)= ocean i U (Φ F):= by
 refine Sync.drape (peak (h.volume0 hp.sync)) (h.volume0 (turn hp).sync) (fun n=>?_) hi
 change Hue.flip _ (ocean n _ F n)=_
 rw [lamp h hp.sync n,lamp h (turn hp).sync n, Rock.LinearMapRealm, spinC (F n) _ ( theory hp.price h.price n ) ]; rfl
lemma sOcean (h: Knot b U)(hp: Form0 b F)(i:ℂ)(hi:i∈Town): Φ (ocean i U F)= ocean i U (Φ F):= by
 funext m l; let X(n:ℕ):= twine (fade n) U
 have hx : ∀ n, hue G (ocean i ( X n ) F)=ocean i (X n) (hue G F):= fun n=> shOcean (tried h (fade n ) (being n) (sold n)) hp i hi
 obtain he := lean (carries (steak hp) (newer h) hi) l; obtain hl:= lean (carries (steak (turn hp)) (newer h) hi ) l
 obtain hb:Tendsto (fun n=>Φ (ocean i (X n) F) m l) atTop (𝓝 ( Φ (ocean i U F) m l )):= by simp_rw [ spark ]; exact he.const_mul _
 simp_rw [hx] at hb; exact tendsto_nhds_unique hb hl
lemma litS (h:Shine.Lift f F): Shine.Lift (fun i=> Φ (f i)) (Φ F):= by obtain ⟨g,R,hr,hg,h,rfl⟩:= h; exact ⟨_,R,hr,hv hg,h.mono fun i hi=> congr_arg _ hi,rfl⟩
lemma live (h:Live f): Live (fun i=>Φ (f i)):= h.elim fun _ h=> Exists.intro _ (litS h)
lemma hot (h:mer f): mer (fun i=>Φ (f i)):= by obtain ⟨u,h⟩:=h; refine ⟨u,?_⟩; rw [altitude, show paid u (fun i=> Φ (f i))= (fun i=>Φ (paid u f i)) from funext (fun i=> (map_smul Φ (i^u) _).symm) ]; exact live h
lemma sun (h:Sun b f): Sun b (fun i=>Φ (f i)):= ⟨hot h.mer,(sunny h).mono fun _ hi=> (turn hi).token⟩
lemma symmH (h: Rock.sym F): Rock.sym (Φ F):= by intro m l i j k; rw [spark,spark,h m]; simp only [List.length_append,List.length_cons]; exact mul_left_comm ..
lemma issueH (h: Issue r F) : Issue r (Φ F):= by intro m l hl; rw [spark,h m _ hl,mul_zero]
lemma colorH (ξ:G.El)(F:Rack G m): repeatC ξ (Hue.flip _ F)= Hue.flip _ ( repeatC ξ F ):= by
 funext l; induction l generalizing F with| nil=> simp [flip_at] | cons x l ih=> rw [repeat_cons,flip_at,repeat_cons]; simp only [List.length_cons, ss, flip_cons,map_neg, ih, Pi.neg_apply, flip_at, mul_neg, neg_mul,Finset.mul_sum,Finset.sum_neg_distrib ]; congr 1; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..
lemma collarH (h: Collar r F): Collar r (Φ F):= ⟨symmH h.sym, ( by intro m x; change repeatC x ( Hue.flip _ _ )=_; rw [colorH, h.color]; rfl ), by intro i w hW; rw [spark,h.ghost i _ hW,mul_zero]⟩
lemma rear (h:Sight F): Sight (Φ F):= by intro m l; rw [spark,spark,h m,star_mul']; simp [invertMom]
lemma fineH (h: Fine b q f): Fine b q (fun i=>Φ (f i)):= ⟨sun h.tune,h.ghost.mono fun _ hi=> collarH hi, show realAlong _ _ from Eventually.mono h.sense fun _ hi=> rear hi⟩
lemma top (h: Cap0 b r q f): Cap0 b r q (fun i=>Φ (f i)):= ⟨fineH h.fine,h.cap.mono fun _ hi=> issueH hi⟩
end YM.FVA2.Hue
