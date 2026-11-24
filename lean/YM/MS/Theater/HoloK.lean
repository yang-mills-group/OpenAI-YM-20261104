import YM.MS.Lifting.Span
import YM.MS.Theater.Value

set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge} {h k:ℕ} {v:ℤ} {p q:Pol G} {f:Local.BV.Grade G} {J:Type}
variable (u:G.El)
def pony (u:G.El)(h:ℕ): Module.End ℝ ( LightC J G h ) where
   toFun f:= ⟨fun i=>(G.adjoint u).toContinuousLinearMap.compContinuousMultilinearMap (f.val i),fun i v s=> congr_arg (G.adjoint u) (f.property i v s) ⟩
   map_add' x y:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro s; exact map_add (G.adjoint u) ..
   map_smul' c x:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro s; exact map_smul (G.adjoint u) c _
lemma commuteSnow (u:G.El)(f:LightC J G (h+1))(p:E4): pony u h ( snow J G h p f ) = snow J G h p ( pony u (h+1) f ):= by
   apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro s; exact map_smul ( G.adjoint u ) (h+1:ℝ) _
lemma colorR (f:Feet G h): radialX G h ( pony u h f )= pony u (h+1) ( radialX G h f ):= by
   apply light_ext; intro a p; rcases a with ⟨ ⟩; change _= G.adjoint u ( diagonal _ _ ); rw [tBudget,tBudget,map_sum]; exact Finset.sum_congr rfl fun i _=>( map_smul (G.adjoint u) ( p i ) _ ).symm
lemma gradP (f:Head G (h+1)): pony u h (gradS G h f)=gradS G h ( pony u (h+1) f):= by
   apply Subtype.ext; ext1 i; exact congr_fun (congr_arg Subtype.val ( commuteSnow u f ( basis i ) )) ()
lemma ruler (X:Feet G h): carve G h ( pony u h X )= pony u h ( carve G h X ):= by rw [carveΩ,carveΩ,map_sub,map_smul,colorR,gradP]
lemma seatPaint (v:Feet G (h+1)): yard G h ( pony u ( h+1 ) v )= Taylor.paint u ( yard G h v ):= by
   apply seatI; rw [taxiY, ruler ]; rfl
lemma coloring (p:FourP)(v:G.Color)(i:J): pony u h (speak h i p v)= speak h i p (G.adjoint u v):= by
   apply Subtype.ext; ext1 j; apply ContinuousMultilinearMap.ext; intro x; change G.adjoint u ((planeC i h (fixF p) v).val j x)=_; unfold speak; by_cases ht:j=i; · rw [ ht, wearing ]; rw [wearing,map_smul,map_smul]
   rw [away _ _ _ ht, away _ _ _ ht ]; exact map_zero _
def spectra (h:ℕ)(a:J)(p:FourP): G.Color →ₗ[ℝ] LightC J G h where
    toFun v:= speak h a p v
    map_add' x y:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro p'; change (planeC a h _ _).val i _=( planeC a h _ x ).val i p'+( planeC a h _ y ).val i p'; by_cases he:i=a; rw [ he,wearing,wearing,wearing, smul_add, smul_add ]; repeat rw [ away h _ _ he ]; simp
    map_smul' c x:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro p'; change (planeC a h _ ( c • x ) ).val i _= c • (( planeC a h _ x ).val i p'); by_cases he:i=a; rw [ he,wearing,wearing ]; module; rw [ away h _ _ he,away h _ _ he ]; simp
lemma Lot (i:CI G): G.adjoint u ( cl G i )= ∑ j:G.ColorIndex, weight u i j • cl G j:= by
    have he(k): cl G k=eb G k:=( EuclideanSpace.basisFun_apply .. ).symm; simp_rw [he]; exact (Landau.color_sum (G.adjoint u ( eb G i ))).symm
lemma tagT (X:Witness G h): advance u ( RowLeg G h X )= RowLeg G h ( X.comp ( Taylor.paint u ) ):= by
   funext i; rcases i with ⟨⟨⟨_|i,_|_⟩,t⟩,p⟩ <;> first | (solve| exact (seedStar.mp (Color.stays u ( wholeℓ X ).1)).real' _ ( by norm_num [ghostNo,ghostChannel] ))| skip
   change (∑ j:G.ColorIndex,wc u t j * ( item i (X.comp ( yard G h )) j p ))= item i ( ( X.comp ( Taylor.paint u ) ).comp ( yard G h )) t p;
   unfold item; rw [ show ((X.comp _).comp _) _=X ( Taylor.paint u (yard G h ( speak (h+1) i p (cl G t) )) ) from rfl,← seatPaint,coloring,Lot ]; -- no match ambiguous underscore
   have he : speak (h+1) i p ( ∑ j:G.ColorIndex,weight u t j • cl G j )= ∑ j:G.ColorIndex,weight u t j • speak (h+1) i p (cl G j):= by
       change spectra ( h+1 ) i p _=_; simp_rw [map_sum,map_smul]; rfl
   rw [he]; simp_rw [ map_sum,map_smul, Finset.mul_sum, LinearMap.comp_apply ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ wc, Complex.real_smul ]; ring
lemma labelU (p:Pol G): repeatC u ( orbit G p ) = orbit G ( changed (fun _=> Labels.Taylor.paint u) p ):= by
    let L(i:ℕ):= Labels.Taylor.paint ( G:=G ) ( j:=i ) u; induction p using MvPolynomial.induction_on with
    | C x =>
       rw [changed,MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, cus, band0,map_smul,advance_nil ]
    | mul_X t i h =>
       simp_rw [map_mul,bags,cusp,Lifting.linkC,h]; rw [ ← dawnB, advance_bud, advance_nil, lamp, tagT,dawnB ]; rw [ moved_v L i, pageX ]; -- match
    | add p q hp hq=> simp only [map_add,hp,hq]
end YM.MS.Theater
