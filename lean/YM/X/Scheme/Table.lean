import YM.X.Bare.Light
import YM.X.Rank.Fall
/-!
Real finite smeared D, constructed nested (zoom on D is the lower D) and parity equivariant. Universal left inverse on tangent = square. Not dependent on actual data.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Pert Pert.Position Function Filter Set Maxwell Maxwell.Free
open scoped Topology BigOperators Classical
variable {G:Gauge} (F:Labels.Frames G) {d e : ℕ}
local notation "L" => Buffer F
local notation "H" => jacBank F (pureBank F d)
local notation "A" => Bank F

-- finite linear lookup submodule (factor via lookie of REAL-using sections only, real part)
section
variable {F} {X Y : Type*} [AddCommGroup X][Module ℝ X][AddCommGroup Y][Module ℝ Y]
def tableSpace (F:Labels.Frames G)(d:ℕ)(X : Type*)[AddCommGroup X][Module ℝ X] : Submodule ℝ (Bank F d→ₗ[ℝ] X) := Submodule.span ℝ (range (fun (v:Pert.Position.Section F d × X)=> (project F v.1).smulRight v.2))
local notation "R" => tableSpace F
lemma table_column (v : Section F d)(x:X) : (project F v).smulRight x ∈ tableSpace F d X:= Submodule.subset_span ⟨(v,x),rfl⟩
lemma table_post (v:X→ₗ[ℝ] Y){s:A d→ₗ[ℝ] X}(hs:s∈ R d X) : v.comp s ∈ R d Y:= by
   induction hs using Submodule.span_induction with
   | mem t he=> obtain ⟨x,rfl⟩:=he; convert! table_column x.1 (v x.2) using 1; exact LinearMap.ext (fun q=>map_smul v _ _)
   | zero=> simp
   | add x y hx hy h g=> rw [LinearMap.comp_add]; exact Submodule.add_mem _ h g
   | smul c t _ h=> rw [LinearMap.comp_smul]; exact Submodule.smul_mem _ _ h
lemma table_pull (v:E F d→ₗ[ℂ] E F e){s:A d→ₗ[ℝ] X}(hs:s∈ R d X): s ∘ₗ pulls v ∈ R e X:= by
   induction hs using Submodule.span_induction with
   | mem t he=> obtain ⟨x,rfl⟩:=he; exact table_column (F:=F) (d:=e) ⟨x.1.r,v ∘ x.1.p,x.1.f⟩ x.2 -- defeq?
   | zero=> simp
   | add x y hx hy h g=> rw [LinearMap.add_comp]; exact Submodule.add_mem _ h g
   | smul c t _ h=> rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ h
end

def Recip (D:A d→ₗ[ℝ] L d) : Prop:= D ∘ₗ H = LinearMap.id

def augD (D:A d→ₗ[ℝ] L d) (S:A (d+1)→ₗ[ℝ] L (d+1)) := S + splitB F (show d≤d+1 from d.le_succ) ∘ₗ (D ∘ₗ pulls (up F (show d≤d+1 from d.le_succ))+ ((-1:ℝ) • (zoomL F (show d≤d+1 from d.le_succ) ∘ₗ S)))
lemma augD_light (D:A d→ₗ[ℝ] L d) (S:A (d+1)→ₗ[ℝ] L (d+1)) (hD : Recip F D) (hS:Recip F S): Recip F (augD F D S):= by
   unfold Recip
   ext1 x -- unfold
   let U:= pulls (up F (show d≤d+1 from d.le_succ)); let Y:= zoomL F (show d≤d+1 from d.le_succ); let W:= jacBank F (pureBank F (d+1)) x
   have ht:S W=x:= DFunLike.congr_fun hS x
   change S W + splitB F (show d≤d+1 from d.le_succ) (D (U W)+ (-1:ℝ) • Y (S W))=x; rw [ht]; unfold U W; rw [← jacBank_zoom, pure_zoom, show D (H _) = Y x from DFunLike.congr_fun hD (Y x),neg_one_smul ℝ (M:=Buffer F d),add_neg_cancel,map_zero,add_zero]
lemma augD_zoom (D:A d→ₗ[ℝ] L d) (S:A (d+1)→ₗ[ℝ] L (d+1))(x:A (d+1)) : zoomL F (show d≤d+1 from d.le_succ) (augD F D S x)=D (pulls (up F (show d≤d+1 from d.le_succ)) x):= by
   dsimp only [augD,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply]; rw [map_add,splitB_right,neg_one_smul ℝ (M:=Buffer F d)] ; abel

def colorD (D:A d→ₗ[ℝ] L d) := (1/2:ℝ) • (D+ cPar F ∘ₗ D ∘ₗ pulls (par F d))
lemma colorD_par (D:A d→ₗ[ℝ] L d)(x): colorD F D (pulls (par F d) x)=cPar F (colorD F D x):= by simp only [colorD,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,pulls_p,map_smul,map_add,cPar_cycle]; rw [add_comm]
lemma colorD_light (K:Bare.Shop F)(D:A d→ₗ[ℝ] L d)(hD:Recip F D):Recip F (colorD F D) := by
   apply LinearMap.ext; intro x
   have he t : D (H t)=t:= DFunLike.congr_fun hD t
   change colorD F D (H x)=x; simp only [colorD,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.add_apply,he]; rw [← jacBank_par,K.all_par,he,cPar_cycle,← two_smul ℝ,smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul]
lemma aug_tables {D:A d→ₗ[ℝ] L d} {S:A (d+1)→ₗ[ℝ] L (d+1)} (hD:D∈tableSpace F d (Buffer F d))(hS:S∈ tableSpace F (d+1) (Buffer F (d+1))): augD F D S ∈ tableSpace F (d+1) (Buffer F (d+1)):= Submodule.add_mem _ hS (table_post _ (Submodule.add_mem _ (table_pull _ hD) (Submodule.smul_mem _ _ (table_post _ hS))))
lemma color_tables {D:A d→ₗ[ℝ] L d}(h:D∈ tableSpace F d (Buffer F d)): colorD F D ∈ tableSpace F d (Buffer F d):= Submodule.smul_mem _ _ (Submodule.add_mem _ h (table_post _ (table_pull _ h)))

lemma beginD (hg:G.Simple)(d : ℕ): ∃ D:A d→ₗ[ℝ] L d,D∈tableSpace F d (Buffer F d) ∧ Recip F D:= by
   obtain ⟨k,s,h⟩:= finite_detectors F d (frozen F d hg)
   obtain ⟨g,hg⟩:= LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=(Buffer F d)) (V':=Fin k → ℝ) _ h
   let D:= ∑ i:Fin k,(project F (s i)).smulRight (g (Pi.single i 1)); refine ⟨D,Submodule.sum_mem _ (fun i _=> by exact table_column (X:=Buffer F d) (s i) (g (Pi.single i 1))),?_⟩
   refine LinearMap.ext (fun v=> ?_); let V:Fin k→ℝ:= LinearMap.pi (fun i=> feedback F d (s i)) v
   show D (jacBank F (pureBank F d) v)=v
   haveI : IsZeroApply (A d →ₗ[ℝ] L d) (A d) (L d):= by constructor; intro x; rfl
   haveI : IsAddApply (A d →ₗ[ℝ] L d) (A d) (L d):= by constructor; intros; rfl
   unfold D; rw [_root_.sum_apply] -- cash
   simp only [LinearMap.smulRight_apply,pureJac]
   simp_rw [show ∀ (i:Fin k),feedback F d (s i) v=V i from fun i=> rfl] -- simp
   -- scaled basis
   conv_rhs => rw [show v=g V from Eq.symm (DFunLike.congr_fun hg v)]
   simp_rw [← map_smul g (V _) (Pi.single _ 1),← map_sum]
   congr 1
   funext i; rw [Finset.sum_apply]; simp [Pi.single_apply]

structure Detector (F:Labels.Frames G) (d:ℕ) where
   D:Bank F d→ₗ[ℝ] Buffer F d
   finiteD : D∈tableSpace F d (Buffer F d)
   fixed : Recip F D
   color (x:Bank F d): D (pulls (par F d) x)= cPar F (D x)

variable (hg:G.Simple)(K:Bare.Shop F)
def fresh (d:ℕ): Detector F d:= ⟨ colorD F ((beginD F hg d).choose),color_tables F (beginD F hg d).choose_spec.1,colorD_light F K _ (beginD F hg d).choose_spec.2,colorD_par F _⟩
set_option maxRecDepth 4096
def nextD (D:Detector F d): Detector F (d+1):=
   let x:= fresh F hg K (d+1)
   ⟨colorD F (augD F D.D x.D),color_tables F (aug_tables F D.finiteD x.finiteD), colorD_light F K _ (augD_light F _ _ D.fixed x.fixed),colorD_par F _⟩
lemma next_zoom (D:Detector F d)(x): zoomL F (show d≤d+1 from d.le_succ) ((nextD F hg K D).D x)= D.D (pulls (up F (show d≤d+1 from d.le_succ)) x):= by
   unfold PositionX.nextD; dsimp only [colorD,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply]; rw [map_smul,map_add,augD_zoom,zoomL_par F,augD_zoom,pulls_par,D.color,cPar_cycle,← two_smul ℝ,smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul]

def nested (d:ℕ):Detector F d:= match d with | 0=> fresh F hg K 0 | d+1=>nextD F hg K (nested d)
lemma zoom_compat (h:d≤e)(x:A e) : zoomL F h ((nested F hg K e).D x)=(nested F hg K d).D (pulls (up F h) x):= by
   induction e,h using Nat.le_induction with
   | base=>rw [zoomL_same,pulls_same]
   | succ e h ih=> rw [← zoomL_mul F h e.le_succ, nested, next_zoom, ih,pulls_up]
end YM.PositionX
