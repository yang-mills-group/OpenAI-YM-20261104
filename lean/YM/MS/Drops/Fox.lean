import YM.MS.Drops.Chord
import YM.MS.Drops.Reeds
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
open Next.Rank.Radian
open Breeze Next Next.Rank Next.Rank.Beamer Asymptotics
variable {G:Gauge}{h k r:ℕ}
abbrev Hoop (G:Gauge)(k:ℕ):= Lattice.PlaqAxes × ( Fin k→ Axis )× G.ColorIndex
abbrev Ep (i:Hoop G k): Degree G:= ⟨i.1,i.2.2,0,k,i.2.1⟩
lemma ahead (x:Hub G (k+2) k): ∃ i:Hoop G k, x.val=Ep i:= by
    rcases x with ⟨⟨a,b,p,i,v⟩,h1,h2,h3⟩; change p=0 at h1; change k ≤ i at h2; change i+2≤k+2 at h3; have h:i=k:= by omega
    subst p i; exact ⟨ ⟨a,v,b⟩,rfl ⟩
lemma petals (u:Key G): ∃ t:Hoop G u.1→ℝ,(axes G u.1|>.coord u.2)=∑ i,t i • stand (Ep i):= by
   let f (i:Hoop G u.1) : Module.Dual ℝ (Taylor G u.1):= stand ( Ep i ); let U:= span ℝ ( Set.range f ); have hp : U.dualCoannihilator=⊥:= by
       refine le_antisymm (fun x hx=> ( Submodule.mem_bot _ ).mpr (judges u.1 (d:=u.1+2) le_rfl x 0 ?_) ) bot_le; apply funext; intro t; obtain ⟨p,h⟩:= ahead t; change gesture t.val ( sweep u.1 x )= gesture t.val ( sweep u.1 0 ); rw [map_zero,map_zero,h]; exact (Submodule.mem_dualCoannihilator x).mp hx ( f p ) ( subset_span (Set.mem_range_self p) )
   have hv : U=⊤ := by
       apply Submodule.eq_top_of_finrank_eq; rw [ Subspace.dual_finrank_eq ]; have he:= Subspace.finrank_add_finrank_dualCoannihilator_eq U; rw [ hp ] at he; simpa using he
   obtain ⟨c,hc⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp ( show (axes G u.1|>.coord u.2)∈U from hv ▸ Submodule.mem_top ); exact ⟨c, hc.symm.trans (by rw [ Finsupp.sum ]; apply Finset.sum_subset ( Finset.subset_univ .. ); intro i hi ht; rw [ Finsupp.notMem_support_iff.mp ht,zero_smul ] )⟩ -- fn cap argument
abbrev petal (u:Key G): Hoop G u.1→ ℝ:= (petals u).choose
abbrev slope (u:Key G) : Maxwell.Probe G u.1:= ( axes G u.1|>.coord u.2 ).comp ( gaugeJet (G:=G) )
lemma slope_p (u:Key G): slope u= ∑ i,petal u i • (stand (Ep i)).comp ( gaugeJet (G:=G) ):= by
    unfold slope; rw [ ( petals u ).choose_spec ]; apply LinearMap.ext; intro t; simp only [LinearMap.comp_apply]; rw [ LinearMap.sum_apply ( M:=Taylor G u.1 ) (σ₁₂:=RingHom.id ℝ),LinearMap.sum_apply (M:=Maxwell.Shell G u.1) (σ₁₂:=RingHom.id ℝ) ]; rfl
lemma grow (u:Key G): Theater.lamp u=∑ i:Hoop G u.1, (↑(petal u i):ℂ) • fax (Ep i):= by
    unfold Theater.lamp pick; rw [ ( petals u ).choose_spec ]; rw [ show Complex.ofRealCLM.toLinearMap.comp ( ∑ i:Hoop G u.1,( petals u ).choose i • stand ( Ep i ) : Module.Dual ℝ ( Taylor G u.1 ) )= ∑ i:Hoop G u.1,(↑(petal u i):ℂ) • (Complex.ofRealCLM.toLinearMap.comp (stand ( Ep i ))) from ?_ ]; rw [map_sum]; apply Finset.sum_congr rfl; intro i hi; exact map_smul ( RowLeg G u.1 ) _ _ -- syntax Lean named sum
    apply LinearMap.ext; intro p; rw [LinearMap.comp_apply, LinearMap.sum_apply (σ₁₂:=RingHom.id ℝ) (M:=Taylor G u.1), map_sum, LinearMap.sum_apply (σ₁₂:=RingHom.id ℝ) (M:=Taylor G u.1) ]; apply Finset.sum_congr rfl; intro i hi; change ( (petal u i* stand (Ep i) p:ℝ):ℂ)= (petal u i:ℂ)*( ( stand (Ep i) p:ℝ ):ℂ); push_cast; rfl
lemma singer_g (u:Key G)(x:QP): chair G x (singer (Theater.lamp u))=∑ i:Hoop G u.1,(↑(petal u i):ℂ) • chair G x (singer (fax (Ep i))):= by
    rw [ grow ]; let M : Local.BV.Grade G→ₗ[ℂ] Law G:= { toFun := singer, map_add' f g:= by funext l; rcases l with _|⟨i,_|x⟩<;> first | rfl| (exact (zero_add _).symm), map_smul' c f:= by funext l; rcases l with _|⟨i,_|x⟩ <;> first | rfl | (exact (mul_zero _)|>.symm) };
    change chair G x ( M _ )=_; simp_rw [map_sum,map_smul]; rfl
-- symmetric arrays.We define key pair.D.Dot.T. For every t eventual.Shape coherence.Identity.C.
local notation "P" => Hoop G
abbrev sizeL (i:Key G) : ℕ:= i.1+2
structure FieldCert (Z:E4→ℝ→ℂ)(i j:Key G): Prop where
    tall t x: Z x t= ( exp t ^ ( sizeL i+sizeL j ) )⁻¹ • Z ( (exp t)⁻¹ • x ) 0
    wind x : Outlay atTop ( Z x ) ( -( ((sizeL i+ sizeL j ):ℕ):ℤ ) )
    up x : Tall0 ( Z x )
    speak (a b: E4)(x:ℝ): HasDerivAt ( Z (a-b) ) ( -linkD G x (chair G (out a) (singer (Theater.lamp i))) ( chair G ( out b ) (singer (Theater.lamp j)) ) [] ) x -- - applied Op?
    fees (x:E4): x≠0→ Sharp0 (fun t=>Z x t- (legKernel (slope i) (slope j) x:ℂ))
end YM.MS.Drops
