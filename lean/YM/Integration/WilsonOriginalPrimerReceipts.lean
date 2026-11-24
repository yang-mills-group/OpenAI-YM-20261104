import YM.Integration.WilsonOriginalPrimerRollJet
import YM.Integration.WilsonOlderFreshGraphArmada
import YM.QuadraticLocal.Fk.Capsule

/-! The complete funded teacher's scalar marked receipts on the original
absolute links, including the positive-support reindexing used to mount its
rows on the Wilson binder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerReceipts
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary PositionX.Jet PositionX.Gauss
open AllOrder AllOrder.Fire AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphMount
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}

def head (Y:Lantern G Unit)(x:Site n)(l e:ℕ)(A:Link G n):ℝ:=
  if l≤e then Radial.jet (Helmet.frame Y.atom x) (e-l+Y.r) A else 0

private theorem curved (Y:Lantern G Unit)(x:Site n)(l d e:ℕ)(rank:Y.r≤l+d+1)(A:Link G n):
    someJ (fun t:ℝ=>t^(l+d+1-Y.r)*Y.atom.unmasked (Haiku.life (fun _=>A) t) x)
      (e+d+1)=head Y x l e A:=by
  let u:rule Unit n:=fun _=>1
  have unity:Ink.invoice x Y.roots u=1:=by simp [Ink.invoice,Ink.paid,u,Function.comp_def]
  have eq:=WilsonOriginalPrimerLampJet.earned Y x u l d e rank (fun _=>A) contDiffAt_const
  rw [weigh_const] at eq
  change _=Y.gleam x u l e A at eq
  rw [Lantern.gleam,Lantern.frame_cross] at eq
  by_cases h:l≤e <;> simpa [Lantern.light,unity,head,h] using eq

theorem located (W:Roll G Unit)(l d e:ℕ)(d0:0<d){a C:ℝ}(ha:0<a)
    (paid:W.Faith {()} () (l+d+2) a C)(x:Site n)(A:Link G n):
    HasSum (fun z:{u:W.Ty // 0<(W.leg u).atom.magnitude}=>head (W.leg z.1) x l e A)
       ((W.folded l e).table n (mingle A (WilsonElectedPrimaryTensor.pin x))):=by
  have rank (u:W.Ty):(W.leg u).r≤l+d+1:=by
    have upper:(W.leg u).r+(W.leg u).roots.length≤l+d+2:=(paid.pinned u).tall
    have owned:0<(W.leg u).roots.length:=List.length_pos_of_mem (paid.pinned u).owns
    omega
  let v (u:W.Ty):=head (W.leg u) x l e A
  have supported:Function.support v ⊆ {u|0<(W.leg u).atom.magnitude}:=by
    intro u hu
    by_contra hn
    have blank (U:Config G n):(W.leg u).atom.unmasked U x=0:=
      Bloom.awaken _ U x (le_antisymm (le_of_not_gt hn) (Texture.mag_nonneg _))
    apply hu
    simp only [v,←curved (W.leg u) x l d e (rank u),blank,mul_zero,someJ,iteratedDeriv_const]
    split <;> simp
  apply (hasSum_subtype_iff_of_support_subset supported).2
  have eq:=WilsonOriginalPrimerRollJet.original W l d e d0 ha paid x (fun _=>A) contDiffAt_const
  rw [weigh_const] at eq
  exact eq.congr_fun (fun u=>(curved (W.leg u) x l d e (rank u) A).symm)

variable {Q d:ℕ}{α:Type}{P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)(weight:α→ℂ)
local notation "M" => material S W C σ paid legal d0 weight

theorem painted (z:Name W)(t:α)(e:ℕ)(A:Link G n):
    (M z).paint t * Complex.ofReal ((M z).markReceipt e A) =
      weight t * (head ((W z.1).leg z.2.1) S.center z.1 e A:ℝ):=by
  let Y:=(W z.1).leg z.2.1
  let c:=fare Y σ
  have pos:0<c:=mul_pos z.2.2 (Real.exp_pos _)
  have chart : Helmet.frame (Bloom.letdown Y.atom c⁻¹) S.center=
      c⁻¹ • Helmet.frame Y.atom S.center:=by
    funext A; exact Bloom.grant Y.atom c⁻¹ _ S.center
  have scale (k:ℕ):Radial.jet (Helmet.frame (Bloom.letdown Y.atom c⁻¹) S.center) k A=
      c⁻¹ * Radial.jet (Helmet.frame Y.atom S.center) k A:=by
    rw [chart]; unfold Radial.jet
    rw [iteratedFDeriv_const_smul_apply (Helmet.frameGrade Y.atom S.center|>.smooth.of_le le_top)]
    simp only [smul_apply,smul_eq_mul]; ring
  change ((c:ℝ):ℂ)*weight t * Complex.ofReal (if z.1.val≤e then Radial.jet
      (Helmet.frame (Bloom.letdown Y.atom c⁻¹) S.center) (e-z.1.val+Y.r) A else 0)=
      weight t*Complex.ofReal (if z.1.val≤e then Radial.jet (Helmet.frame Y.atom S.center)
        (e-z.1.val+Y.r) A else 0)
  split <;> rename_i h
  · rw [scale]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr pos.ne']
  simp

end YM.Integration.WilsonOriginalPrimerReceipts
end
