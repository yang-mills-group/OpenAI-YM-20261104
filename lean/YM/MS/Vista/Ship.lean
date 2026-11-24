import YM.MS.Vista.Muse
/-!
# Meeting with localized pull-phase. Burn whenever center external distance too. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Scale I}{μ ν:I→Measure QP}
 {K L:I→Latch.Edge G}{X Y:I→ Law G}{A B:I→Cover}{z a x y:I→ℝ}{p:Bool}{h k:ℕ}{w l r:Wire ( BH G ) E QP}
local notation "Γ"=> field ( parity (C:=G.ColorIndex ) ( A:=Axis ))
abbrev Window (p:Bool)(A B:I→Cover)(μ:I→Measure QP)(K:I→Latch.Edge G)(F H:I→Law G)(i:I): Law G:= PairV p (μ i) (A i) ( B i ) ( K i ) (F i) ( H i )
def αmesh (b:Bool)(K:I→Latch.Edge G)(F H:I→Law G)(i j:BH G)(l r:Wire ( BH G ) E QP)(t:I) (p:QP× E):= viν b (K t) i j ( F t ) ( H t ) (sail l p.2) (sail r p.2) p.1
lemma Φmesh (h: Fund S K z)(hx: Lease false true S X x)(hv: Lease false true S Y y)(hp:Split l r w)(i j:BH G): pole S (αmesh p (tinted K) X Y i j l r ) ( HoopT S w z (x*y) ):= by
    let L:= ContinuousLinearMap.fst ℝ QP E; let V:= ContinuousLinearMap.snd ℝ QP E; let T:= (moneyL p)∘L L; let R:= (i,L):: Wire.lift l V; let W:=(j,T)::Wire.lift r V; let u:ℂ:=2*cross (parity j) (degree Γ l ); obtain hm : Bound S (Plane.Chart X R) ( Qbud R S x ):= hx ( E:=QP× E ) R (fun v=> Bool.noConfusion v) (fun _=> by simp [ R ] ); obtain hL : Bound S (Plane.Chart Y W) ( Qbud W S y ):= hv ( E:=QP× E ) W (fun v=> Bool.noConfusion v) (fun _=> by simp [ W ]);
    have h': Bound S (fun i q=>Plane.Chart X R i q * Plane.Chart Y W i q) ( Qbud R S x * Qbud W S y ):= Costs.mul hm hL; obtain ht:= Rapid.mul ( tint h i j|>.rapid (F:=E) ) h'; convert ht.L (ContinuousLinearMap.mul ℝ ℂ u) using 1; · ext; unfold αmesh viν; simp only [sail_degree, ContinuousLinearMap.mul_apply', Plane.Chart,R,W,T,V,sail_cons,lift_sail,L]; unfold u; rw [ContinuousLinearMap.comp_apply, walkL ]; ring_nf; rfl
    funext t; unfold HoopT Qbud positive R W pitch; rw [field_cons, field_cons, field_lift,field_lift,show S.length t ^4=S.length t ^(4:ℤ) from rfl]; obtain hu: fieldDim wfield l+fieldDim wfield r=fieldDim wfield w:= w_mass hp; simp only [Pi.mul_apply]; calc
       _=S.length t^ ((4:ℤ)+fieldDim wfield w)*(z t*x t*y t):= by rw [ zpow_add₀ (S.pos t).ne' ]; ring
       _= _:= by rw [show (4:ℤ)+fieldDim wfield w=(4-wfield i-wfield j)+(wfield i+fieldDim wfield l)+(wfield j+fieldDim wfield r) from (by omega),zpow_add₀ ( S.pos t ).ne', zpow_add₀ (S.pos t ).ne' ]; ring
abbrev hbill (p:Bool)(ν:I→Measure QP)(B:I→Cover)(i j:BH G)(K:I→ Latch.Edge G)(F H:I→Law G) (l r:Wire (BH G) E QP):= waveInt (fun i=> be ( B i )) ν (αmesh p (tinted K) F H i j l r)
lemma h_toned (h:Fund S K z)(he:Visible X)(hf: Visible Y)(p:Bool)(i:I)(j k:BH G)(x y:Lengths G)(L:Cover) : ContDiff ℝ ∞ ( fun q=> be L q * viν p ( K i ) j k ( X i ) ( Y i ) x y q ) := by
    have hp:= touch_mesh p (A_Fr h i) j k ( station_t x ) ( station_t y ) (he.2 i) (hf.2 i) (contDiff_const (c:=0)) (K:=id) contDiff_id; simp_rw [station_w] at hp; exact (be_sm L).mul hp
lemma h_learn (hf:Fund S K z)(he:Visible X)(hm: Visible Y)(i:I)(p:Bool)(j k:BH G)(x y:Lengths G)(A:Cover): pinQ (fun q=> be A q * viν p ( K i ) j k ( X i ) ( Y i ) x y q) := by
    intro u v huv; have hx: congrQ ( Opp p u ) ( Opp p v ):= by cases p; exact huv.opp; exact huv
    unfold viν; simp only [ show be A u= _ from (φ_per A huv) , hf.perk i j k huv, show ∀ s:BH G,X i ((s,u)::x)=X i ((s,v)::x) from fun z=> he.1 i _ _ ( .cons ⟨rfl,huv⟩ (asc _)), show ∀c:BH G, Y i ((c,Opp p u)::y)=Y i ((c,Opp p v)::y) from fun c=> hm.1 i _ _ ( .cons ⟨ rfl,hx ⟩ (asc _) ) ];
lemma ηfold (H:VistaQ S μ ν)(he:Fund S K z)(hx:Visible X)(hy:Visible Y)(x':E)(t:I)(i j: BH G): hbill p ν B i j K X Y l r t x'=
   ∫ q,be ( B t) q * viν p ( K t ) i j ( X t ) ( Y t ) (sail l x') (sail r x') q ∂μ t := by
    unfold hbill waveInt; rw [ ← H.folds _ _ ( h_learn he hx hy t p i j (sail l x') (sail r x') (B t) ) (h_toned he hx hy p t i j _ _ _ |>.continuous) ]; -- order parameters? µ.L
    congr 1; ext; unfold αmesh; simp only [viν,tinted]; ring
lemma harborK (H:VistaQ S μ ν)(he:Fund S K z)(hx:Visible X)(hy:Visible Y)(w:Wire ( BH G ) E QP)(i:I)(x:E): Plane.Chart ( Window p A B μ K X Y ) w i x=scatter Γ w (fun l r=>be ( A i ) ( net l x )*(∑ j:BH G,∑ k:BH G, hbill p ν B j k K X Y l r i x )):= by unfold Plane.Chart Window PairV; simp_rw [ sail_scatter,sail_net,ηfold H he hx hy ]
lemma knock (H:VistaQ S μ ν)(he:Fund S K z)(hx:Visible X)(hy:Visible Y)(H0:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ l r w:Wire (BH G) E QP, Split l r w → Bound S (fun i x=>be ( A i ) (net l x)*(∑ j:BH G,∑ k:BH G,hbill p ν B j k K X Y l r i x)) (Qbud w S a)): Lease false false S ( Window p A B μ K X Y ) a := by
    intro E _ _ w hx' _; unfold Cape; rw [show Plane.Chart ( Window p A B μ K X Y ) w= _ from funext fun t=> funext (harborK H he hx hy w t (p:=p) (A:=A) ( B:=B )) ]; exact gather_bound w (fun l r hl=> H0 E _ _ _ hl)
-- ordinary proof without burn.Geometry distance.Marker.High.Est.
abbrev Mileage (S:Scale I)(A:I→Cover)(v:I→ℝ):= paid S ( fun i=> ‖embed (A i)‖ ) v
lemma ηserve (he:Lease false true S X x)(ht: Lease false true S Y y)(h:Fund S K z)(H:VistaQ S μ ν)(_hx:nn x)(_hy:nn y)(_hz:nn z)(hM:Split l r w)(i j: BH G) : Bound S ( hbill p ν B i j K X Y l r ) ( Qbud w S ( z*x*y ) ) := by
   convert Wavepay ( U:=fun i=> be ( B i )) (fun _=> sailor _) H.sector ( Φmesh h he ht hM i j (p:=p)) ( H.mint E ) using 1; funext i'; exact ( ( Cash (S:=S) i' z (x*y) w )|>.trans (by simp only [ Qbud,Pi.mul_apply ]; rw [ ← mul_assoc (z i') ] ) )|>.symm -- unused nn exc
lemma murmur (he:Lease false true S X x)(ht: Lease false true S Y y)(h:Fund S K z)(H:VistaQ S μ ν)(hT:Visible X)(hF:Visible Y)(hp:Mileage S A S.length)(hx:nn x)(hy:nn y)(hz:nn z): Lease false false S ( Window p A B μ K X Y) ( z*x*y ) := by
    apply knock H h hT hF; intro E _ _ l r w hw; refine pulse_bill (net l) ?_ ( paid_at hp (fun i=>S.pos i|>.le) ); refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=> ηserve he ht h H hx hy hz hw i j ) ?h ) ?h; exact fun i _ _=> pos_nn _ ( joy ( joy hz hx ) hy ) _ i
end YM.MS.Vista
