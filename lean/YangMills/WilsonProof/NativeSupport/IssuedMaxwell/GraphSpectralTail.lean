import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphTail
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphSpectator
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphSpectralTail
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.Scale YM.FVA2.Scale.Equator YM.FVA2.Dframe YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

theorem seated (a:Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))(k:ℕ)(y:Points m):
    read g (1+m) k (Fin.append (fun _:Fin 1=>a) b) (forest 0 y)=
    read g (m+1) k (Fin.cons a b) (WithLp.toLp 2 (Fin.cons 0 y.ofLp)):=by
  rw [GraphSpectator.root g (Nat.one_add m),GraphSpectator.first]
  unfold forest
  change read _ _ _ _ (WithLp.toLp 2 (GraphSpectator.recut _ (Fin.append (0:Points 1).ofLp y.ofLp)))=_
  rw [GraphSpectator.first]
  rfl

theorem original (a:Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))(k:ℕ)(y:Points m):
    read g (m+1) k (Fin.cons a b) (WithLp.toLp 2 (Fin.cons 0 y.ofLp))=
      ∑s:GraphTail.entry g b,GraphTail.income g b s*read g (m+1) k (Fin.cons a (labels g (GraphTail.marks g b s)))
        (WithLp.toLp 2 (Fin.cons 0 y.ofLp)):=by
  rw [←seated,GraphTail.expanded]
  refine Finset.sum_congr rfl fun s _=>?_
  rw [seated]

theorem corners {W J S:Type*}[Fintype W][Fintype J][Fintype S](f:W→J→S→ℂ):
    (∑w,∑j,∑s,f w j s)=∑s,∑w,∑j,f w j s:=by
  calc
    _=∑w,∑s,∑j,f w j s:=Finset.sum_congr rfl fun _ _=>Finset.sum_comm
    _=_:=Finset.sum_comm

theorem truncated (p:Ordinary.Price (B g) n)(b:Fin m→Ordinary.Label (B g))(e h k:ℕ)
    (t:ℝ)(x:Points n)(y:Points m):
    Ordinary.truncation (B g) (read g) p e h k b t x y=
      ∑s:GraphTail.entry g b,GraphTail.income g b s*
        Ordinary.truncation (B g) (read g) p e h k (labels g (GraphTail.marks g b s)) t x y:=by
  let a (w:Fin (h+1))(j:Fin (k+1)):Ordinary.Label (B g):=⟨w.val,p w.val j.val t x⟩
  let scale (w:Fin (h+1)):ℂ:=Real.exp (((e:ℝ)-(w.val:ℝ))*t)
  let node:Points (m+1):=WithLp.toLp 2 (Fin.cons (0:YangMills.Spacetime) y.ofLp)
  let half (w:Fin (h+1))(j:Fin (k+1))(s:GraphTail.entry g b):ℂ:=
    scale w*read g (m+1) (k-j.val) (Fin.cons (a w j) (labels g (GraphTail.marks g b s))) node
  calc
    _=∑w,∑j,∑s,GraphTail.income g b s*half w j s:=by
      unfold Ordinary.truncation
      refine Finset.sum_congr rfl fun w _=>?_
      refine Finset.sum_congr rfl fun j _=>?_
      rw [original,Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _=>?_
      change scale w*(GraphTail.income g b s*_) =GraphTail.income g b s*(scale w*_)
      ring
    _=∑s,∑w,∑j,GraphTail.income g b s*half w j s:=corners _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      simp only [Ordinary.truncation,Finset.mul_sum,half,a,scale,node]
end IssuedMaxwell.GraphSpectralTail
end
