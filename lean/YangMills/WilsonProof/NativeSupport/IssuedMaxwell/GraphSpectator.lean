import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCover
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphSpectator
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.Scale YM.FVA2.Scale.Equator
open PowerSeries YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

abbrev recut {A:Type*}(h:n=m)(v:Fin n→A):Fin m→A:=v ∘ Fin.cast h.symm
theorem root (h:n=m)(a:Fin n→Ordinary.Label (B g))(k:ℕ)(x:Points n):
    read g n k a x=read g m k (recut h a) (WithLp.toLp 2 (recut h x.ofLp)):=by
  subst m
  rfl

theorem first {A:Type*}(a:Fin 1→A)(b:Fin m→A):
    recut (Nat.one_add m) (Fin.append a b)=Fin.cons (a 0) b:=by
  rw [Fin.append_left_eq_cons]
  funext i
  rfl

theorem joined (u:Scan g.core n)(v:Scan g.core m):
    labels g (Fin.append u v)=Fin.append (labels g u) (labels g v):=by
  funext i
  let label (q:Q g.core):Ordinary.Label (B g):=⟨heft q,cap q (le_refl _)⟩
  change label (Fin.append u v i)=_
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [Fin.append_left,Fin.append_left]
    rfl
  · intro j
    rw [Fin.append_right,Fin.append_right]
    rfl

theorem original (v:Scan g.core m)(p:Q g.core)(y:Points m)(k:ℕ):
    coeff k (lonelyG (install (wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)))
      y p v)=read g (m+1) k (Fin.cons ⟨heft p,cap p (le_refl _)⟩ (labels g v))
        (WithLp.toLp 2 (Fin.cons 0 y.ofLp)):=by
  change coeff k (install _ _ (forest 0 y) (Fin.append (Single p) v))=_
  rw [← GraphCorrelation.original,joined,root g (Nat.one_add m),first]
  unfold forest
  change read _ _ _ _ (WithLp.toLp 2 (recut _ (Fin.append (0:Points 1).ofLp y.ofLp)))=_
  rw [first]
  rfl
end IssuedMaxwell.GraphSpectator
end
