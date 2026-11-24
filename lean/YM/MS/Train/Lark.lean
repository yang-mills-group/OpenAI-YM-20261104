import YangMills.WilsonProof.NativeSupport.YM.MS.Train.MeasureD
/-!
# ${loop}$ convolution independent of dimensional index. Magnez linear regular path
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open Signal Book Convolve
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F Z:Flats G}{f:Coat G}{U:Rip G}
-- extend all $zeta$ with same spine. knot f etc preserve when actual.
def tapeL (M:ℂ→ MH (Mob G)) : MH (Coat G) := { toFun x z:= M z (x z),map_smul' c x:= funext fun i=>map_smul (M i) c (x i),map_add' x y:= funext fun i=> map_add (M i) (x i) (y i) }
def tapeB (M: Oceans.Pair G) : Signal.Pair (Coat G) where
   toFun f:= tapeL (fun i=> M (f i))
   map_add' x y:= LinearMap.ext fun u=> funext fun i=>map_add (M.flip (u i)) (x i) (y i)
   map_smul' c x:= LinearMap.ext fun u=> funext fun i=>map_smul (M.flip (u i)) c (x i)
def blast (n:ℕ)(M:MH (Coat G)): MH (Flats G):= Finsupp.lsum ℂ fun i:ℕ=> (Finsupp.lsingle (i+n):Coat G→ₗ[ℂ] Flats G).comp M
lemma blap (X: Flats G)(i:ℕ)(M: MH (Coat G)) : blast i M X=X.sum (fun j x=> Finsupp.single (j+i) (M x)):=rfl
lemma blast_sl (n m:ℕ) (M:MH (Coat G))(f:Coat G): blast n M (Finsupp.single m f)=Finsupp.single (m+n) (M f):= Finsupp.lsum_single .. -- possibly ζ
variable {k m n:ℕ}
lemma blade (i:ℕ)(F: Flats G)(M: MH (Coat G)) (n:ℕ): (blast i M F) (n+i) = M (F n):= by
   rw [blap,Finsupp.sum_apply,Finsupp.sum]; by_cases h:n∈ F.support
   · rw [Finset.sum_eq_single n]; simp; · intro k _ hk; simp [hk]
     exact fun x=> (x h).elim
   · rw [Finsupp.notMem_support_iff.mp h,map_zero]; refine Finset.sum_eq_zero fun j hj=>?_ ; have he:j≠n:= by intro he; exact h (he ▸ hj)
     simp [he]
lemma bland {i:ℕ}(p:m < i)(M:MH (Coat G))(F:Flats G): blast i M F m=0:= by
   rw [blap,Finsupp.sum_apply,Finsupp.sum]; exact Finset.sum_eq_zero fun j hj=> Finsupp.single_eq_of_ne (by omega : m≠j+i)
-- δ product. use Finsupp.lsum for left and shift for right. angle.
def explode (M:Signal.Pair (Coat G)) : Signal.Pair ( Flats G):= Finsupp.lsum ℂ fun i:ℕ=> {
   toFun u:= blast i (M u)
   map_smul' c u:= by apply LinearMap.ext; intro x; simp only [LinearMap.smul_apply, RingHom.id_apply,map_smul,blap,Finsupp.sum]; simp only [ Finset.smul_sum,Finsupp.smul_single]
   map_add' u v:= by apply LinearMap.ext; intro A; simp only [map_add,LinearMap.add_apply,blap,Finsupp.sum,Finsupp.single_add, Finset.sum_add_distrib] }
lemma explosionP (M:Signal.Pair (Coat G)): explode M X= X.sum fun i x=> blast i (M x):= rfl
lemma explodeL (M:Signal.Pair (Coat G))(X Y:Flats G): explode M X Y=X.sum (fun i x=>Y.sum (fun j y=> Finsupp.single (j+i) (M x y))):= by rw [explosionP]; unfold Finsupp.sum; rw [LinearMap.sum_apply]; rfl
lemma explode_zero (M:Signal.Pair (Coat G))(X Y:Flats G) : explode M X Y 0=M (X 0) (Y 0):= by
    rw [explosionP,Finsupp.sum,LinearMap.sum_apply, Finset.sum_apply']; by_cases hv:0∈ X.support
    · rw [Finset.sum_eq_single 0]; exact blade ..; · intro i hi he; exact bland (by omega:0 < i) ..
      exact fun h=> (h hv).elim -- orientation
    rw [Finsupp.notMem_support_iff.mp hv,map_zero,LinearMap.zero_apply]; exact Finset.sum_eq_zero fun i hi=> bland (show 0 < i from Nat.pos_of_ne_zero (fun h=> hv (h ▸ hi))) .. -- omega membership relation not solved
end YM.MS.Train
