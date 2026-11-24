import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.Next.RANK.Radian.Indices
/-!
# Free poles: transverse symbol for each derivative of curvature.Engineering degree.
Use redundant Plaq and layout alphabet so extension to every tensor is attained. Matched to
actual Maxwell derivative form (cf §). Here Fourier momentum p; L² heat in radian normalization later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer -- verify
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}
abbrev reel (G:Gauge)(h:ℕ)(i j:Axis): Feet G (h+1)→ₗ[ℝ] Tensor.T E4 G.Color h:= (LinearMap.proj j).comp ( ( DeckC Axis G h ).subtype ∘ₗ stepL G Axis h i )
def Δ (G:Gauge)(h:ℕ)(i j:Axis): Feet G (h+1)→ₗ[ℝ] Tensor.T E4 G.Color h:= reel G h i j - reel G h j i
lemma reel_h (X: Feet G (h+1))(i j:Axis): diagonal (reel G h i j X) = grad i ( diagonal (X.val j) ):= workL (basis i) X j
lemma Δ_walk (i j:Axis)(A: Head G (h+2)) : Δ G h i j ( gradS G ( h+1 ) A )=0:= by
    let X:=gradS G (h+1) A; change reel _ _ i j X-reel _ _ j i X=0; apply sub_eq_zero.mpr; apply ext_diag _ _ ((stepL G Axis h i X).property j) ((stepL G Axis h j X).property i); funext x; change diagonal (reel _ _ i j X) x=diagonal (reel _ _ j i X) x; rw [reel_h,reel_h]; change grad i (diagonal ((stepL G Unit (h+1) j A).val ())) x=grad j (diagonal ((stepL G Unit (h+1) i A).val ())) x; unfold stepL; rw [workL, workL]; exact commuteD (( diag_smooth _ 2 ).contDiffAt) _ _ -- arg x infer
lemma Curvy (A:Labels.Taylor G h)(i j:Axis): takeCurl A i j= Δ G h i j (step_in G h A):= by
    unfold takeCurl; push_cast; rw [smul_sub]; rfl
lemma growH (X:Feet G (h+1))(i j:Axis): takeCurl (yard G h X) i j=Δ G h i j X:= by rw [ Curvy,taxiY,carveΩ,map_sub,map_smul,Δ_walk,smul_zero,sub_zero ]
variable (L K:Degree G)
abbrev stand (L: Degree G): Module.Dual ℝ ( Taylor G L.degree ):= gesture L ∘ₗ sweep L.degree
abbrev fax (L:Degree G) := RowLeg G L.degree ( Complex.ofRealCLM.toLinearMap.comp ( stand L ) )
lemma stand_K (x:Taylor G L.degree): stand L x=( L.degree.factorial:ℝ )*(takeCurl x L.a.val.1 L.a.val.2 ( basis ∘ L.layout ) L.paint):= by unfold stand; rw [LinearMap.comp_apply,gesture_hits,show Beamer.sweep L.degree x=inspect x from rfl, Beamer.inspected,CellsInt.test_top]; rfl
-- layout.MZ
abbrev GlowD (L:Degree G)(p:FourP): ℂ:= I ^ ( L.degree ) * ∏ i, (p (L.layout i):ℂ)
abbrev axisC (i j k:Axis)(p: FourP): ℂ:= if k=j then I*(p i) else if k=i then -(I*(p j)) else 0
lemma photo (i:Axis)(c:G.ColorIndex)(p:FourP): fax L (W i c p)= if c=L.paint then GlowD L p*axisC L.a.val.1 L.a.val.2 i p else 0 := by
    let j:= L.a.val.1; let k:= L.a.val.2; let d:= L.degree; have hn:j≠k:= ( show j<k from L.a.property ).ne; let s:= speak d i p ( cl G c ); let V:= basis ∘ L.layout; change I^(d+1)*(stand L _ :ℂ)=_; rw [ stand_K ];
    change I^(d+1)*((↑((d.factorial:ℝ) * ( takeCurl ( yard G d ( speak (d+1) i p ( cl G c ) ) ) j k V L.paint:ℝ ))):ℂ)=_
    rw [growH, show (Δ G d _ _ _) = p j • s.val k - p k • s.val j from ?_ ]; swap; · unfold s Δ reel; rw [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.comp_apply, step_at, step_at ]; rfl
    have H (k:Axis): s.val k V L.paint=if k=i ∧ c=L.paint then Theater.amount d*∏ i,p (L.layout i) else 0:= by
       by_cases he:k=i; · subst k; by_cases hx:c=L.paint <;> simp [V,s,speak,d,cl,wearing,hx,eq_comm]; exact Or.inl (Finset.prod_congr rfl fun i _=> (lean_axis _ _).symm)
       rw [Theater.away _ _ _ he, if_neg (by tauto) ]; simp -- away uses s? need unfold
    change _=( if _ then GlowD L p* axisC j k i p else 0 ); simp only [ sub_apply, smul_apply, PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,H,axisC,GlowD ]; unfold d at *
    by_cases hp:c=L.paint; swap; · simp [hp]
    simp only [if_pos hp, eq_comm (a:=i) (b:=k), eq_comm (a:=i) (b:=j) ]; simp only [hp,and_true]; have hnΓ:( L.degree.factorial:ℂ )≠0:= by exact_mod_cast Nat.factorial_ne_zero _;
    split_ifs <;> first | (solve| grind)| (simp [Theater.amount,Complex.ofReal_prod] <;> field_simp <;> ring)
end YM.MS.Drops
