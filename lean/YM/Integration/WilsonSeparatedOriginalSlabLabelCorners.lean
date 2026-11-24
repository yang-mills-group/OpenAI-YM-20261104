import YM.Integration.WilsonWholeLimit
import YM.RG17.Gathers

/-! Simultaneous convergence of genuine cutoff-dependent field coordinates over a compact set of separated lattice configurations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabLabelCorners
open Finset Function Filter Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Overlay Work.G08 Bid Next.Rank Next.UVStress Price OPE Extraction Spec Cells OPE.Cards
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {n:ℕ} {l:Filter (ℕ×ℕ)}

theorem uniform (F:Final C f S)(E:Services C f S)(K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n)
    (d:Caps n)(a:C.book.Vector d)(w:(ℕ×ℕ)→C.book.Vector d)(law:l≤f.fuse)
    (converges:∀i,Tendsto (fun k=>w k i) l (𝓝 (a i))) {ε:ℝ}(positive:0<ε):
    ∀ᶠ k in l, ∀z:Fin n → Cover, tag (C.S.a k.1) z∈K →
      ‖C.ensemble d (wrap (C.side k.1 k.2) ∘ z) (w k) - S.value d (tag (C.S.a k.1) z) a‖<ε:=by
  let B (i) := dial (L:=C.book) d i
  let J := (i:Fin n)→(C.book.coord (d i)).Index
  letI:Fintype J:=Pi.instFintype
  let Y (r:J) i := B i (r i)
  let W (v:C.book.Vector d)(j:J):=∏i,(B i).repr (v i) (j i)
  have expand (X:Moment C.book n d)(v:C.book.Vector d):X v=∑j:J,W v j*X (Y j):=by
    have decomp:v=fun i=>∑k,(B i).repr (v i) k • B i k:=funext fun i=>((B i).sum_repr _).symm
    conv_lhs=>rw [decomp]
    rw [MultilinearMap.map_sum];exact Finset.sum_congr rfl fun j _=>X.map_smul_univ (fun i=>(B i).repr (v i) (j i)) _
  let η:=ε/(Fintype.card J +1:ℝ)
  have ep:0<η:=div_pos positive (by positivity)
  have per (j:J):∀ᶠ k in l,∀z:Fin n → Cover,tag (C.S.a k.1) z∈K→
      ‖W (w k) j * C.ensemble d (wrap (C.side k.1 k.2) ∘ z) (Y j) - W a j * S.value d (tag (C.S.a k.1) z) (Y j)‖≤η:=by
    let v(i:Fin n):C.book.Token:=⟨d i,Y j i⟩
    have continuous:ContinuousOn (fun x=>S.read x v) K:=((S.smooth_read F.room.kernel.smooth v).continuousOn).mono separated
    obtain ⟨M, bound⟩:=compact.exists_bound_of_continuousOn continuous
    let H:=‖W a j‖+|M|+2
    have hp:0<H:=by dsimp [H];positivity
    let κ:=η/H
    have kp:0<κ:=div_pos ep hp
    have hW:Tendsto (fun k=>W (w k) j) l (𝓝 (W a j)):=
      tendsto_finsetProd _ fun i _=>((B i).coord (j i)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (converges i)
    have base : ∀ᶠ k:ℕ×ℕ in f.fuse,∀z:Fin n → Cover,tag (C.S.a k.1) z∈K→dist (Extraction.lifted C k.1 k.2 v z) (S.read (tag (C.S.a k.1) z) v)<κ:=
      RGReadout.Literal.cornerLimit E v K compact separated κ kp
    have fine:=base.filter_mono law
    filter_upwards [fine,Metric.tendsto_nhds.mp hW (min κ 1) (lt_min kp zero_lt_one)] with k fine close
    intro z hz
    let A:=C.ensemble d (wrap (C.side k.1 k.2) ∘ z) (Y j)
    let A₀:=S.value d (tag (C.S.a k.1) z) (Y j)
    have variation:‖A-A₀‖≤κ:=by
      have closeSite:=fine z hz
      change dist (C.numeric k.1 k.2 v (wrap _ ∘ z)) (S.read _ v)<κ at closeSite
      change dist A A₀<κ at closeSite
      rw [dist_eq_norm] at closeSite
      exact closeSite.le
    have size:‖A₀‖≤|M|:=(bound _ hz).trans (le_abs_self _)
    rw [dist_eq_norm] at close
    have shift:‖W (w k) j-W a j‖≤κ:=(lt_min_iff.mp close).1.le
    have magnitude:‖W (w k) j‖≤‖W a j‖+1:=by
      calc ‖W (w k) j‖=‖(W (w k) j-W a j)+W a j‖:=by rw [sub_add_cancel]
        _≤_:=by grw [norm_add_le, (lt_min_iff.mp close).2.le];exact le_of_eq (add_comm _ _)
    change ‖W (w k) j*A-W a j*A₀‖≤η
    calc ‖W (w k) j*A-W a j*A₀‖=‖W (w k) j*(A-A₀)+(W (w k) j-W a j)*A₀‖:=by congr 1;ring
      _≤(‖W a j‖+1)*κ+κ*|M|:=by grw [norm_add_le,norm_mul,norm_mul,magnitude,variation,shift,size]
      _≤η:=by have paid:κ*H=η:=div_mul_cancel₀ η hp.ne';rw [←paid];dsimp [H];nlinarith [kp.le]
  filter_upwards [eventually_all.mpr per] with k hk
  intro z hz
  rw [expand (C.ensemble d _),expand (S.value d _),←Finset.sum_sub_distrib]
  calc ‖∑j:J,_‖≤∑j:J,η:= (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _=>hk j z hz)
    _<ε:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];dsimp [η];rw [mul_div_assoc',div_lt_iff₀ (by positivity)];nlinarith

end YM.Integration.WilsonSeparatedOriginalSlabLabelCorners
