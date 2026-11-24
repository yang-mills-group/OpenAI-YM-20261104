import YM.FormalBulk08.Avenue.Lance
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open scoped Matrix.Norms.Frobenius
open Wilson
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l r:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
open Rial Planned.PrimaryIntegral295 Place Carrier Film Next.Foundations
lemma unwinds {T Y: Anthem D G}(F:Frame G d)(s:Signed)(H:Hol G)(hp:Clef o T r)(ht:Clef o Y r)(h:∀ (p:Studio D)(w:chain (edgeL G) r), T p 0 r (dart s∘ w) = Y (Dawn.froth s D p) 0 r w * ∏ i,City.banner s (bearing (w i)) ) (x: Letter F): pearlJ F (T (Pose.inside F x D) 0 r) (mint F x)=∑ y∈mates F s x, coeff 0 (lariat F s x y)*pearlJ F (Y (Pose.inside F y D) 0 r) (mint F y):= by
   let p:= Pose.inside F x D; let Q:= froth s D p
   let a':=mint F x; let m:= Pose.slots F x; let n:=label F x
   let t:=slate (T p 0 r) d m; let S:=slate (Y Q 0 r) d m
   obtain ⟨w,B,hw,hb,hV⟩:=hp.fare.2.2 0 r; obtain ⟨v,C,hC,hv,hU⟩:=ht.fare.2.2 0 r
   have Ht (u:Fin m→Snap G d): t u=S (turnIn G d s∘u):= (wind_slate s H o (T p 0 r) (Y Q 0 r) (h p) hw (hV p) hC (hU Q) u).symm
   have hz : F.coords (lent t n) = F.act s.ortho (F.coords (lent S n)):= by
       rw [Frame.act_coords, preserve s t S (monic_slate _ _ H hw (hV p) (perfumed T hp p _ _) d m) (monic_slate _ _ H hC (hU Q) (perfumed Y ht Q _ _) d m) (slotsFits F x) n (F.bound a') Ht]
   change (F.coords (lent t n) a').re= _; rw [hz,real_scores]; rw [show family F a'=family F (mint F x) from rfl,← swims F s x]; apply Finset.sum_congr rfl; intro y hy; have hp':Rial.Crew F s x y:=(Finset.mem_filter.mp hy).2
   let b : ℝ:= Dawn.tone (pet F x).val s
   have hk : Q=b • Pose.inside F y D:= by unfold Q Pose.inside p; rw [Pose.inside,breezy]; rw [hp'.1]; rfl
   have hy : (Y Q 0 r)= b • (Y (Pose.inside F y D) 0 r):= by rw [hk,ht.map_smul];rfl
   rw [lariat,if_pos hp',coeff_zero_C]
   have hm : (F.grades (mint F y)).2=m := congr_arg Prod.snd hp'.2
   have hq : (F.grades (mint F y)).1=n := congr_arg Prod.fst hp'.2
   change (Pose.pocket F S n _).re*_=(b* _)*_
   unfold S pearlJ; rw [hy,hm,hq,slate_scale (hU _) hC,Pose.stip]; simp [mul_comm,mul_left_comm,a',mul_assoc]
lemma wood_harmony (F:Frame G d)(s:Signed)(H:Hol G)(v:Train j)(k:ℝ)(hj:4≤j)(hk:0<k)(Y:Roof.Plaza F D)(o:Loc G 1)(hp:Court o F Y)(ht:Harmonized F s Y): preTable (lariat F s)*Woven F v k Y=Woven F v k Y*preTable (lariat F s):= by
    have he i: Clef o (Y i) d:= clef_through (hp.officers i) (slotsFits F _); ext x i; let T:= Y i; let Z:=larch Y (lariat F s) i; let U:= preTable (lariat F s); let n:=slots F x; let S:= mates F s x
    have hz : Clef o Z d := Clef.sum Finset.univ _ (fun j _=> (he j).launch _)
    obtain ⟨a,ha,Ht⟩:=completed v hk hj (from_clef (he i) 0) n; obtain ⟨b,hb,hB⟩:= completed v hk hj (from_clef hz 0) n
    have hu p (w:chain (edgeL G) n): b p 0 n (dart s ∘ w)=a (Dawn.froth s D p) 0 n w*∏ i,City.banner s (bearing (w i)) := by rw [hB,Ht]; exact wave_spin s (ht i) v hk hj hz.fare (he i).fare p w
    symm; rw [Matrix.mul_apply,Matrix.mul_apply]; change (∑ j,clover F v k (Y j) d x * U j i)=∑ j,U x j*clover F v k T d j
    change (∑ j,clover F v k (Y j) d x*coeff 0 (lariat F s j i))= _; rw [←clover_align F v hk hj Y (lariat F s) he x i]
    change pearlJ F (winner v k d Z (Pose.inside F x D) n) (mint F x)=_; rw [←hB,unwinds F s H hb ha hu]; apply Eq.trans _ (Finset.sum_subset (Finset.subset_univ S) (f:=fun j=>U x j*clover F v k T d j) (?_)); swap
    · intro j _ hj; rw [show U x j=0 from ?_,zero_mul]; change coeff 0 (if _ then _ else _)=_;rw [if_neg (show ¬Rial.Crew F s x j from fun h=>hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)),map_zero]
    apply Finset.sum_congr rfl; intro j hj; rw [Ht]; unfold clover; rw [← (crew_rank F s ((Finset.mem_filter.mp hj).2)).1];rfl
lemma canopy_limit {E R:ℕ}{F:Frame G d}{T:SectionData F}{ρ:ChartRatio G}{H:Source.Hol G}(h:Use W ρ E)(q:Quota F H W o D E R)(v:LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb: Bid.pop T)(u:Extras W)(hD:d≤R)(a:hue G)(x:Leaf W.scrolls)(s:Signed): preTable (lariat F s)*WLimit W a ρ F T q.horizon x=WLimit W a ρ F T q.horizon x * preTable (lariat F s):= by
    let U:= WLimit W a ρ F T q.horizon x; let M (n:ℕ):= WLocal W a ρ F T q.horizon x n; have hv (i j):Ends (fun k=>M k i j) (U i j):= struckW h q v hs ht hb hD u a x i j; let Z:=preTable (lariat F s)
    ext i j;have hH:Ends (fun k=>(Z*M k) i j) ((Z*U) i j):= by simp_rw [Matrix.mul_apply]; exact tendsto_finsetSum _ (fun s _=>(hv s j).const_mul _)
    have hp:Ends (fun k=>(M k *Z) i j) ((U*Z) i j):= by simp_rw [Matrix.mul_apply];exact tendsto_finsetSum _ (fun s _=> (hv i s).mul_const _)
    refine tendsto_nhds_unique (hH.congr' (?_)) hp; filter_upwards [eventually_ge_atTop x.b] with n hn; exact congr_fun (congr_fun (wood_harmony F s H (location _ _ _) K.penalty ((W.V x.a).clock.adm x.b) K.penalty_pos _ o (birth a v q hs ht hb _ _ _ x.zone hn) (harmony a v q hs ht hb _ _ n x.zone hn s)) i) j


lemma homotheties (a:Axis)(k ε:ℝ)(j t:ℕ)(p:Momentum): Train.levelD k (Train.top j) a p= Train.levelD ε (Train.top t) a p:= by
    unfold Train.levelD; rw [feed_top,feed_top]; simp [Train.levelNoise,Train.stream,Train.nozzle]
lemma cardin (W:Lab G K I)(a: hue G)(ρ:ChartRatio G)(F:Frame G d)(T:Source.SectionData F)(h:d+1≤D)(x:Leaf W.scrolls): WLocal W a ρ F T h x x.b= Woven F (Train.top 4) 1 (sectionY T h):= by
    rw [WLocal,bornY,terrace_zero]; let A:= (W.V x.a); let v:=Train.top (A.clock.J x.b)
    rw [show location _ x.b x.b=v from ?_]; swap; · unfold location; rw [Nat.sub_self]; rfl
    have he: bandP G v K.penalty=bandP G (Train.top 4) 1:= by
       unfold bandP reins stall buckle fieldD scaleD; simp_rw [show ∀ p a, v.levelD K.penalty a p = _ from fun p a=> homotheties a K.penalty 1 _ 4 p]
    ext i j; unfold Woven clover winner; rw [he]
end YM.FormalBulk08.Avenue
