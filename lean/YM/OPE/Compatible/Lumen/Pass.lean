import YM.OPE.Compatible.Lumen.Hips
/-!
# Orbit Gram factor polar. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore
attribute [local instance] Gauge.frobInner
variable (H: Even n.val) (T:Plot H)
local notation "TK" => Keys G (Limb H)
local notation "VK" => Keys G (Node H)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
abbrev rainbow {E:Type}[Fintype E] (u v:Keys G E):= ∑ i:E,inner ℝ (u i) (v i)
def ruby (G:Gauge)(E:Type)[Fintype E](u:Keys G E): Dual' (Keys G E):= { toFun v:= rainbow u v,map_add':= fun x y=> by unfold rainbow; simp only [Pi.add_apply,inner_add_right,Finset.sum_add_distrib], map_smul':= fun c x=> by unfold rainbow; simp [← Finset.mul_sum, inner_smul_right] }
lemma rainbow_nn {E:Type}[Fintype E](u:Keys G E): 0≤ rainbow u u:= Finset.sum_nonneg fun _ _=> real_inner_self_nonneg
lemma rainbow_zero {E:Type}[Fintype E](u:Keys G E)(h: rainbow u u=0):u=0:= by funext i; exact inner_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _=> real_inner_self_nonneg).mp h i (Finset.mem_univ i))
def chargeV (x y:DK):ℝ:= rainbow (rinse H (T.palmFrame G x)) (rinse H (T.palmFrame G y))
lemma chargedW (x:DK)(hx:x≠0): 0< chargeV H T x x:=by
     by_contra! h; let y:=T.palmFrame G x; have hz: rinse H y=0:= rainbow_zero _ (le_antisymm h (rainbow_nn _)); obtain ⟨v,hv⟩:= T.vertical_span x
     have hi:= tideDown H y v; simp only [hv,hz, Pi.zero_apply, inner_zero_right,Finset.sum_const_zero,neg_zero] at hi
     have he : y=0:= rainbow_zero _ hi; apply hx; rw [← T.pedestal x, show T.palmFrame G _= 0 from he,map_zero]
lemma hue (x y:DK): chargeV H T x y=chargeV H T y x:=Finset.sum_congr rfl (fun _ _=>real_inner_comm ..)
lemma quake: ∃ W:Law DK,∀ x y,W.P x y=chargeV H T x y :=by
     have he (x:DK):∃ L:Dual' DK, chargeV H T x=L:=⟨ (ruby G (Node H) _).comp ((rinse H).comp (T.palmFrame G)), rfl⟩
     obtain ⟨P,h⟩:= Libra.giraffe_addendum he (hue H T); exact ⟨Libra.giraffe P (fun x y=> (h _ _).trans ((hue H T _ _).trans (h _ _).symm)) (fun x hx=> (chargedW H T x hx).trans_eq (h _ _).symm), h⟩
def fond (G:Gauge) : Law (Keys G T.Stable):= Classical.choose (quake H T)
lemma fond_L (x y : DK): (fond H T G).P x y= chargeV H T x y:= Classical.choose_spec (quake H T (G:=G)) x y
def ead (x: VK):= fun y:DK=> rainbow x (rinse H (T.palmFrame G y))
def landFuse (G:Gauge): Keys G T.Free→ₗ[ℝ] Keys G T.Stable := (fond H T G).inverse.comp ({
     toFun x:= -(ruby G (Node H) (rinse H (T.rollX x)) |>.comp ((rinse H).comp (T.palmFrame G)))
     map_add' x y:= by apply LinearMap.ext; intro i; simp only [LinearMap.neg_apply,LinearMap.add_apply,LinearMap.comp_apply]; simp [ruby,rainbow,inner_add_left,Finset.sum_add_distrib]; ring
     map_smul' c x:=by apply LinearMap.ext; intro i; simp only [LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.comp_apply]; simp [ruby,rainbow, inner_smul_left,← Finset.mul_sum] } : Keys G T.Free →ₗ[ℝ] Dual' (Keys G T.Stable))
abbrev certain (x: FD):TK:= T.palmFrame G (landFuse H T G x)+ T.rollX x
lemma drains (x:FD): rinse H (certain H T x)=0:=by
     let y:= certain H T x; let P:= fond H T G; let g:= (Pond H).galaxy G; let v:=rinse H y; let m:=landFuse H T G x; have hp(j:DK):chargeV H T m j + rainbow (rinse H (T.rollX x)) (rinse H (T.palmFrame G j))=0:= by rw [←fond_L]; change P.P (P.inverse _) _+_=0; rw [P.applies]; exact neg_add_cancel _
     have ht(i:DK): rainbow v (rinse H (T.palmFrame G i))=0:=by
          rw [show v=rinse H (T.palmFrame G m)+rinse H (T.rollX x) from map_add ..]; unfold rainbow; simp only [Pi.add_apply,inner_add_left,Finset.sum_add_distrib]; exact hp i
     have he:= ht (T.porch G (g v)); rw [T.harp_span (g v) (show g v∈Stand.gaugeRange .. from ⟨v,rfl⟩)] at he
     have hw: g v=0:= rainbow_zero _ (by rw [show rainbow (g v) (g v) = -(rainbow v (rinse H (g v))) from ?_]; simp [he]; exact tideDown H (g v) v -- wrong tideDown S=(gv),v=v yields this
                                       )
     have hx:= tideDown H y v
     apply rainbow_zero; change rainbow v v=0; change _= -rainbow v v at hx; change rainbow (g v) y=_ at hx; rw [hw] at hx; unfold rainbow at *; simpa using hx
end YM.OPE.Cascade.Glass
